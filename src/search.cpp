/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2010 Marco Costalba, Joona Kiiski, Tord Romstad

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <vector>

#include "book.h"
#include "evaluate.h"
#include "history.h"
#include "misc.h"
#include "movegen.h"
#include "movepick.h"
#include "search.h"
#include "timeman.h"
#include "thread.h"
#include "tt.h"
#include "ucioption.h"

#ifdef GPSFISH
#include "position.tcc"
#include "osl/boardTable.h"
using osl::Board_Table;
#include "osl/ptypeTable.h"
using osl::Ptype_Table;
#include "osl/offset32.h"
using osl::Offset32;
#include "osl/checkmate/immediateCheckmate.h"
#include "osl/checkmate/fixedDepthSearcher.h"
#include "osl/checkmate/dfpn.h"
using osl::checkmate::ImmediateCheckmate;
using std::string;
#include "osl/enter_king/enterKing.h"
#include "osl/misc/milliSeconds.h"
#include "osl/checkmate/dfpn.h"
#include "osl/checkmate/dfpnParallel.h"
#include "osl/hash/hashKey.h"
#endif
#ifdef MOVE_STACK_REJECTIONS
#include "osl/search/moveStackRejections.h"
#endif

#ifdef GPSFISH
# define GPSFISH_CHECKMATE3
# define GPSFISH_CHECKMATE3_QUIESCE
# define GPSFISH_DFPN
#endif

namespace Search {

  volatile SignalsType Signals;
  LimitsType Limits;
  std::vector<Move> SearchMoves;
  Position RootPosition;
}

using std::cout;
using std::endl;
using std::string;
using namespace Search;

namespace {

  // Set to true to force running with one thread. Used for debugging
  const bool FakeSplit = false;

  // Different node types, used as template parameter
  enum NodeType { Root, PV, NonPV, SplitPointRoot, SplitPointPV, SplitPointNonPV };

  // RootMove struct is used for moves at the root of the tree. For each root
  // move we store a score, a node count, and a PV (really a refutation in the
  // case of moves which fail low). Score is normally set at -VALUE_INFINITE for
  // all non-pv moves.
  struct RootMove {

    RootMove(){}
    RootMove(Move m) {
      nodes = 0;
      score = prevScore = -VALUE_INFINITE;
      pv.push_back(m);
      pv.push_back(MOVE_NONE);
    }

    bool operator<(const RootMove& m) const { return score < m.score; }
    bool operator==(const Move& m) const { return pv[0] == m; }

#ifdef GPSFISH
    void extract_pv_from_tt_rec(Position& pos,int ply);
#endif
    void extract_pv_from_tt(Position& pos);
#ifdef GPSFISH
    void insert_pv_in_tt_rec(Position& pos,int ply);
#endif
    void insert_pv_in_tt(Position& pos);

    int64_t nodes;
    Value score;
    Value prevScore;
    std::vector<Move> pv;
  };


  /// Constants

  // Lookup table to check if a Piece is a slider and its access function
#ifndef GPSFISH
  const bool Slidings[18] = { 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1 };
  inline bool piece_is_slider(Piece p) { return Slidings[p]; }
#endif

  // Maximum depth for razoring
  const Depth RazorDepth = 4 * ONE_PLY;

  // Dynamic razoring margin based on depth
  inline Value razor_margin(Depth d) { return Value(0x200 + 0x10 * int(d)); }

  // Maximum depth for use of dynamic threat detection when null move fails low
  const Depth ThreatDepth = 5 * ONE_PLY;

  // Minimum depth for use of internal iterative deepening
  const Depth IIDDepth[] = { 8 * ONE_PLY, 5 * ONE_PLY };

  // At Non-PV nodes we do an internal iterative deepening search
  // when the static evaluation is bigger then beta - IIDMargin.
  const Value IIDMargin = Value(0x100);

  // Minimum depth for use of singular extension
  const Depth SingularExtensionDepth[] = { 8 * ONE_PLY, 6 * ONE_PLY };

  // Futility margin for quiescence search
  const Value FutilityMarginQS = Value(0x80);

  // Futility lookup tables (initialized at startup) and their access functions
  Value FutilityMargins[16][64]; // [depth][moveNumber]
  int FutilityMoveCounts[32];    // [depth]

  inline Value futility_margin(Depth d, int mn) {

    return d < 7 * ONE_PLY ? FutilityMargins[std::max(int(d), 1)][std::min(mn, 63)]
                           : 2 * VALUE_INFINITE;
  }

  inline int futility_move_count(Depth d) {

    return d < 16 * ONE_PLY ? FutilityMoveCounts[d] : MAX_MOVES;
  }

  // Reduction lookup tables (initialized at startup) and their access function
  int8_t Reductions[2][64][64]; // [pv][depth][moveNumber]

  template <bool PvNode> inline Depth reduction(Depth d, int mn) {

    return (Depth) Reductions[PvNode][std::min(int(d) / ONE_PLY, 63)][std::min(mn, 63)];
  }

  // Easy move margin. An easy move candidate must be at least this much
  // better than the second best move.
  const Value EasyMoveMargin = Value(0x150);


  /// Namespace variables

  std::vector<RootMove> RootMoves;
  size_t MultiPV, UCIMultiPV, MultiPVIdx;

#ifdef GPSFISH
  Value DrawValue;
#endif
  TimeManager TimeMgr;
  int BestMoveChanges;
  int SkillLevel;
  bool SkillLevelEnabled;
  History H;


  /// Local functions

  Move id_loop(Position& pos, Move* ponderMove);

  template <NodeType NT>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth);

  template <NodeType NT>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth);

  bool check_is_dangerous(Position &pos, Move move, Value futilityBase, Value beta, Value *bValue);
  bool connected_moves(const Position& pos, Move m1, Move m2);
  Value value_to_tt(Value v, int ply);
  Value value_from_tt(Value v, int ply);
  bool can_return_tt(const TTEntry* tte, Depth depth, Value beta, int ply);
  bool connected_threat(const Position& pos, Move m, Move threat);
  Value refine_eval(const TTEntry* tte, Value defaultEval, int ply);
  void update_history(const Position& pos, Move move, Depth depth, Move movesSearched[], int moveCount);
  void do_skill_level(Move* best, Move* ponder);
  int elapsed_time(bool reset = false);
  string score_to_uci(Value v, Value alpha = -VALUE_INFINITE, Value beta = VALUE_INFINITE);
  string speed_to_uci(int64_t nodes);
  string pv_to_uci(const Move pv[], int pvNum, bool chess960);
  string pretty_pv(Position& pos, int depth, Value score, int time, Move pv[]);
  string depth_to_uci(Depth depth);

  // MovePickerExt class template extends MovePicker and allows to choose at
  // compile time the proper moves source according to the type of node. In the
  // default case we simply create and use a standard MovePicker object.
  template<bool SpNode> struct MovePickerExt : public MovePicker {

    MovePickerExt(const Position& p, Move ttm, Depth d, const History& h, Stack* ss, Value b)
                  : MovePicker(p, ttm, d, h, ss, b) {}
  };

  // In case of a SpNode we use split point's shared MovePicker object as moves source
  template<> struct MovePickerExt<true> : public MovePicker {

    MovePickerExt(const Position& p, Move ttm, Depth d, const History& h, Stack* ss, Value b)
                  : MovePicker(p, ttm, d, h, ss, b), mp(ss->sp->mp) {}

    Move get_next_move() { return mp->get_next_move(); }
    MovePicker* mp;
  };

#ifndef GPSFISH
  // Overload operator<<() to make it easier to print moves in a coordinate
  // notation compatible with UCI protocol.
  std::ostream& operator<<(std::ostream& os, Move m) {

    bool chess960 = (os.iword(0) != 0); // See set960()
    return os << move_to_uci(m, chess960);
  }

  // When formatting a move for std::cout we must know if we are in Chess960 or
  // not. To keep using the handy operator<<() on the move the trick is to embed
  // this flag in the stream itself. Function-like named enum set960 is used as
  // a custom manipulator and the stream internal general-purpose array, accessed
  // through ios_base::iword(), is used to pass the flag to the move's operator<<
  // that will read it to properly format castling moves.
  enum set960 {};

  std::ostream& operator<<(std::ostream& os, const set960& f) {

    os.iword(0) = f;
    return os;
  }
#endif

  // is_dangerous() checks whether a move belongs to some classes of known
  // 'dangerous' moves so that we avoid to prune it.
  FORCE_INLINE bool is_dangerous(const Position& pos, Move m, bool captureOrPromotion) {

#ifndef GPSFISH
    // Test for a pawn pushed to 7th or a passed pawn move
    if (type_of(pos.piece_on(move_from(m))) == PAWN)
    {
        Color c = pos.side_to_move();
        if (   relative_rank(c, move_to(m)) == RANK_7
            || pos.pawn_is_passed(c, move_to(m)))
            return true;
    }

    // Test for a capture that triggers a pawn endgame
    if (   captureOrPromotion
        && type_of(pos.piece_on(move_to(m))) != PAWN
        && (  pos.non_pawn_material(WHITE) + pos.non_pawn_material(BLACK)
            - PieceValueMidgame[pos.piece_on(move_to(m))] == VALUE_ZERO)
        && !is_special(m))
        return true;
#endif

    return false;
  }

#ifdef GPSFISH
  void show_tree_rec(Position &pos){
    TTEntry* tte;
    StateInfo st;
    if ((tte = TT.probe(pos.get_key())) != NULL){
      std::cerr << "tte->value=" << tte->value() << std::endl;
      std::cerr << "tte->type=" << tte->type() << std::endl;
      std::cerr << "tte->generation=" << tte->generation() << std::endl;
      std::cerr << "tte->depth=" << tte->depth() << std::endl;
      std::cerr << "tte->static_value=" << tte->static_value() << std::endl;
      Move m=tte->move(pos);
      int dummy;
      if(m != MOVE_NONE
              && pos.is_pseudo_legal(m)
              && !pos.is_draw(dummy)) {
          std::cerr << "move=" << m << std::endl;
          pos.do_undo_move(m,st,
                  [&](osl::Square){ show_tree_rec(pos); }
                  );
      }
    }
  }
#endif
#ifdef GPSFISH
  Value value_draw(Position const& pos){
    if(pos.side_to_move()==osl::BLACK) return DrawValue;
    else return -DrawValue;
  }
#endif  
#ifdef MOVE_STACK_REJECTIONS
  osl::container::MoveStack moveStacks[MAX_THREADS];
  bool move_stack_rejections_probe(osl::Move m, Position const &pos,SearchStack* ss,Value alpha){
    if(DrawValue!=0) return false;
    int i=std::min(7,std::min(ss->ply,pos.pliesFromNull()+1));
    if(i<3) return false;
    osl::state::NumEffectState const& state=pos.osl_state;
    osl::container::MoveStack &moveStack=moveStacks[pos.thread()];
    moveStack.clear();
    while(--i>0) moveStack.push((ss-i)->currentMove);
    osl::Player player=m.player();
    int checkCountOfAltP=pos.continuous_check[osl::alt(player)];
    bool ret=false;
    if(m.player()==osl::BLACK){
      ret=osl::search::MoveStackRejections::probe<osl::BLACK>(state,moveStack,ss->ply,m,alpha,checkCountOfAltP);
    }
    else {
      ret=osl::search::MoveStackRejections::probe<osl::WHITE>(state,moveStack,ss->ply,m,-alpha,checkCountOfAltP);
    }
    return ret;
  }
#endif  
#ifdef GPSFISH
  bool can_capture_king(Position const& pos){
    Color us=pos.side_to_move();
    Color them=flip(us);
    const osl::Square king = pos.king_square(them);
    return pos.osl_state.hasEffectAt(us, king);
  }
#endif  
} // namespace


/// init_search() is called during startup to initialize various lookup tables

void Search::init() {

  int d;  // depth (ONE_PLY == 2)
  int hd; // half depth (ONE_PLY == 1)
  int mc; // moveCount

  // Init reductions array
  for (hd = 1; hd < 64; hd++) for (mc = 1; mc < 64; mc++)
  {
      double    pvRed = log(double(hd)) * log(double(mc)) / 3.0;
      double nonPVRed = 0.33 + log(double(hd)) * log(double(mc)) / 2.25;
      Reductions[1][hd][mc] = (int8_t) (   pvRed >= 1.0 ? floor(   pvRed * int(ONE_PLY)) : 0);
      Reductions[0][hd][mc] = (int8_t) (nonPVRed >= 1.0 ? floor(nonPVRed * int(ONE_PLY)) : 0);
  }

  // Init futility margins array
  for (d = 1; d < 16; d++) for (mc = 0; mc < 64; mc++)
      FutilityMargins[d][mc] = Value(112 * int(log(double(d * d) / 2) / log(2.0) + 1.001) - 8 * mc + 45);

  // Init futility move count array
  for (d = 0; d < 32; d++)
      FutilityMoveCounts[d] = int(3.001 + 0.25 * pow(d, 2.0));
}

/// perft() is our utility to verify move generation. All the leaf nodes up to
/// the given depth are generated and counted and the sum returned.

int64_t Search::perft(Position& pos, Depth depth) {

  StateInfo st;
  int64_t sum = 0;

  MoveList<MV_LEGAL> ml(pos);

  // At the last ply just return the number of moves (leaf nodes)
  if (depth <= ONE_PLY)
      return ml.size();

#ifndef GPSFISH
  CheckInfo ci(pos);
#endif
  for ( ; !ml.end(); ++ml)
  {
#ifdef GPSFISH
      pos.do_undo_move(ml.move(),st,
              [&](osl::Square){
              assert(pos.is_ok());
#else
      pos.do_move(ml.move(), st, ci, pos.move_gives_check(ml.move(), ci));
#endif
      sum += perft(pos, depth - ONE_PLY);
#ifdef GPSFISH
      }
      );
#else
      pos.undo_move(ml.move());
#endif
  }
  return sum;
}


/// think() is the external interface to Stockfish's search, and is called by the
/// main thread when the program receives the UCI 'go' command. It searches from
/// RootPosition and at the end prints the "bestmove" to output.

void Search::think() {

  static Book book; // Defined static to initialize the PRNG only once

  Position& pos = RootPosition;
  elapsed_time(true);
  TimeMgr.init(Limits, pos.startpos_ply_counter());

#ifndef GPSFISH
  // Set output stream mode: normal or chess960. Castling notation is different
  cout << set960(pos.is_chess960());
#endif


  if (Options["OwnBook"].value<bool>())
  {
#ifndef GPSFISH
      if (Options["Book File"].value<string>() != book.name())
          book.open(Options["Book File"].value<string>());
#endif

      Move bookMove = book.probe(pos, Options["Best Book Move"].value<bool>());
      if (bookMove != MOVE_NONE)
      {
          if (!Signals.stop && (Limits.ponder || Limits.infinite))
              Threads.wait_for_stop_or_ponderhit();

#ifdef GPSFISH
          cout << "bestmove " << move_to_uci(bookMove,false) << endl;
#else
          cout << "bestmove " << bookMove << endl;
#endif
          return;
      }
  }

  // Read UCI options: GUI could change UCI parameters during the game
  read_evaluation_uci_options(pos.side_to_move());
  Threads.read_uci_options();

  TT.set_size(Options["Hash"].value<int>());
  if (Options["Clear Hash"].value<bool>())
  {
      Options["Clear Hash"].set_value("false");
      TT.clear();
  }

  UCIMultiPV = Options["MultiPV"].value<size_t>();
  SkillLevel = Options["Skill Level"].value<int>();

  // Do we have to play with skill handicap? In this case enable MultiPV that
  // we will use behind the scenes to retrieve a set of possible moves.
  SkillLevelEnabled = (SkillLevel < 20);
  MultiPV = (SkillLevelEnabled ? std::max(UCIMultiPV, (size_t)4) : UCIMultiPV);

  if (Options["Use Search Log"].value<bool>())
  {
      Log log(Options["Search Log Filename"].value<string>());
      log << "\nSearching: "  << pos.to_fen()
          << "\ninfinite: "   << Limits.infinite
          << " ponder: "      << Limits.ponder
          << " time: "        << Limits.time
          << " increment: "   << Limits.increment
          << " moves to go: " << Limits.movesToGo
          << endl;
  }

  // Wake up needed threads and reset maxPly counter
  for (int i = 0; i < Threads.size(); i++)
  {
      Threads[i].maxPly = 0;
      Threads[i].wake_up();
  }

  // Set best timer interval to avoid lagging under time pressure. Timer is
  // used to check for remaining available thinking time.
  if (TimeMgr.available_time())
      Threads.set_timer(std::min(100, std::max(TimeMgr.available_time() / 8, 20)));
  else
      Threads.set_timer(100);

  // We're ready to start thinking. Call the iterative deepening loop function
  Move ponderMove = MOVE_NONE;
  Move bestMove = id_loop(pos, &ponderMove);

  // Stop timer and send all the slaves to sleep, if not already sleeping
  Threads.set_timer(0);
  Threads.set_size(1);

  if (Options["Use Search Log"].value<bool>())
  {
      int e = elapsed_time();

      Log log(Options["Search Log Filename"].value<string>());
      log << "Nodes: "          << pos.nodes_searched()
          << "\nNodes/second: " << (e > 0 ? pos.nodes_searched() * 1000 / e : 0)
          << "\nBest move: "    << move_to_san(pos, bestMove);

      StateInfo st;
#ifdef GPSFISH
      if(bestMove.isNormal())
          pos.do_undo_move(bestMove,st,
                  [&](osl::Square){
                  assert(pos.is_ok());
#else
      pos.do_move(bestMove, st);
#endif
      log << "\nPonder move: " << move_to_san(pos, ponderMove) << endl;
#ifdef GPSFISH
      } );
#else
      pos.undo_move(bestMove); // Return from think() with unchanged position
#endif
  }

  // When we reach max depth we arrive here even without a StopRequest, but if
  // we are pondering or in infinite search, we shouldn't print the best move
  // before we are told to do so.
  if (!Signals.stop && (Limits.ponder || Limits.infinite))
      Threads.wait_for_stop_or_ponderhit();

  // Could be MOVE_NONE when searching on a stalemate position
#ifdef GPSFISH
  cout << "bestmove " << move_to_uci(bestMove,false);
#else
  cout << "bestmove " << bestMove;
#endif

  // UCI protol is not clear on allowing sending an empty ponder move, instead
  // it is clear that ponder move is optional. So skip it if empty.
#ifdef GPSFISH
  if (ponderMove != MOVE_NONE && Options["Ponder"].value<bool>())
      cout << " ponder " << move_to_uci(ponderMove,false);
#else
  if (ponderMove != MOVE_NONE)
      cout << " ponder " << ponderMove;
#endif

  cout << endl;
}

#ifdef GPSFISH_DFPN
struct CheckmateSolver
{
    osl::checkmate::DfpnTable table_black;
    osl::checkmate::DfpnTable table_white;
    osl::checkmate::Dfpn dfpn[2];
    CheckmateSolver() 
    {
        table_black.setAttack(osl::BLACK);
        table_white.setAttack(osl::WHITE);
        dfpn[playerToIndex(osl::BLACK)].setTable(&table_black);
        dfpn[playerToIndex(osl::WHITE)].setTable(&table_white);
    }
    Move hasCheckmate(Position& pos, size_t nodes) 
    {
        const Depth CheckmateDepth = ONE_PLY*100;
        TTEntry* tte = TT.probe(pos.get_key());
        if (tte && tte->type() == VALUE_TYPE_EXACT
                && tte->depth() >= CheckmateDepth) {
            Value v = value_from_tt(tte->value(), 0);
            if (v >= VALUE_MATE_IN_PLY_MAX || v < VALUE_MATED_IN_PLY_MAX)
                return Move();		// mate or mated
        }

        osl::PathEncoding path(pos.osl_state.turn());
        osl::Move checkmate_move;
        osl::NumEffectState& state = pos.osl_state;
        osl::stl::vector<osl::Move> pv;
        osl::checkmate::ProofDisproof result
            = dfpn[playerToIndex(state.turn())].
            hasCheckmateMove(state, osl::HashKey(state), path, nodes,
                    checkmate_move, Move(), &pv);
        if (result.isCheckmateSuccess()) {
            TT.store(pos.get_key(), value_mate_in(pv.size()),
                    VALUE_TYPE_EXACT, CheckmateDepth, checkmate_move,
                    VALUE_NONE, VALUE_NONE);
            return checkmate_move;
        }
        return Move();
    }
    void clear()
    {
        dfpn[0].clear();
        dfpn[1].clear();
        table_black.clear();
        table_white.clear();
    }
};
struct TestCheckmate
{
    CheckmateSolver *solver;
    Position *pos;
    osl::Move *result;
    uint64_t nodes;
    const Move *moves;
    int first, last;
    TestCheckmate(CheckmateSolver& s, Position& p, osl::Move& r, uint64_t n,
            const Move *pv, int f, int l)
        : solver(&s), pos(&p), result(&r), nodes(n),
        moves(pv), first(f), last(l)
    {
    }
    void operator()(osl::Square) const
    {
        *result = Move();
        if (nodes < (1<<18))
            *result = solver->hasCheckmate(*pos, nodes);
        if (result->isNormal()) {
            if (first > 0)
                std::cout << "info string checkmate in future (" << first
                    << ") " << move_to_uci(moves[first],false)
                    << " by " << move_to_uci(*result,false) << '\n';
        }
        else if (! Signals.stop) {
            Move move;
            TestCheckmate next = *this;
            next.first++;
            next.nodes /= 2;
            next.result = &move;
            if (next.first < last && pos->is_pseudo_legal(moves[next.first])
                    && next.nodes >= 1024) {
                StateInfo st;
                pos->do_undo_move(moves[next.first], st, next);
            }
        }	
    }
};

void run_checkmate(int depth, uint64_t nodes, Position& pos) 
{
    static boost::scoped_ptr<CheckmateSolver> solver(new CheckmateSolver);
    StateInfo st;
    nodes /= 16;
    int mated = 0;
    for (size_t i=0; i<RootMoves.size() && nodes >= 1024 && !Signals.stop; ++i) {
        osl::Move win_move;
        TestCheckmate function(*solver, pos, win_move, nodes,
                &RootMoves[i].pv[0], 0, (i==0) ? depth/2 : 1);
        pos.do_undo_move(RootMoves[i].pv[0], st, function);
        if (! win_move.isNormal())
            nodes /= 4;
        else {
            ++mated;
            RootMoves[i].score = -VALUE_INFINITE;
            //RootMoves[i].non_pv_score = VALUE_MATED_IN_PLY_MAX;
            std::cout << "info string losing move " << i << "th "
                << move_to_uci(RootMoves[i].pv[0],false)
                << " by " << move_to_uci(win_move,false) << '\n';
        }
    }
    solver->clear();
}
#endif

namespace {

  // id_loop() is the main iterative deepening loop. It calls search() repeatedly
  // with increasing depth until the allocated thinking time has been consumed,
  // user stops the search, or the maximum search depth is reached.

  Move id_loop(Position& pos, Move* ponderMove) {

    Stack ss[PLY_MAX_PLUS_2];
    int bestMoveChanges[PLY_MAX_PLUS_2];
#ifdef GPSFISH
    uint64_t es_base[(PLY_MAX_PLUS_2*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)]
#ifdef __GNUC__
      __attribute__((aligned(16)))
#endif
	;
    eval_t *es=(eval_t *)&es_base[0];
#endif
    int depth, delta;
    Value bestValue, alpha, beta;
    Move bestMove, skillBest, skillPonder;
    bool bestMoveNeverChanged = true;

    memset(ss, 0, 4 * sizeof(Stack));
    TT.new_search();
    H.clear();
    RootMoves.clear();
    *ponderMove = bestMove = skillBest = skillPonder = MOVE_NONE;
    depth = delta = 0;
    bestValue = alpha = -VALUE_INFINITE, beta = VALUE_INFINITE;

#ifdef GPSFISH
    ss->currentMove = osl::Move::PASS(pos.side_to_move()); // Hack to skip update_gains
#else
    ss->currentMove = MOVE_NULL; // Hack to skip update gains
#endif

#ifdef GPSFISH
    pos.eval= &es[0];
    *(pos.eval)=eval_t(pos.osl_state,false);
#endif

    for (MoveList<MV_LEGAL> ml(pos); !ml.end(); ++ml)
        if (   SearchMoves.empty()
            || std::count(SearchMoves.begin(), SearchMoves.end(), ml.move()))
            RootMoves.push_back(RootMove(ml.move()));

    // Handle special case of searching on a mate/stalemate position
    if (RootMoves.empty())
    {
        cout << "info" << depth_to_uci(DEPTH_ZERO)
#ifdef GPSFISH
             << score_to_uci(pos.in_check() ? value_mated_in(1) : VALUE_DRAW, alpha, beta) << endl;
#else
             << score_to_uci(pos.in_check() ? -VALUE_MATE : VALUE_DRAW, alpha, beta) << endl;
#endif

        return MOVE_NONE;
    }
#ifdef GPSFISH_DFPN
    uint64_t next_checkmate = 1<<18;
#endif
    // Iterative deepening loop until requested to stop or target depth reached
    while (!Signals.stop && ++depth <= PLY_MAX && (!Limits.maxDepth || depth <= Limits.maxDepth))
    {
        // Save now last iteration's scores, before Rml moves are reordered
        for (size_t i = 0; i < RootMoves.size(); i++)
            RootMoves[i].prevScore = RootMoves[i].score;

        BestMoveChanges = 0;

#ifdef GPSFISH_DFPN
        if ((uint64_t)pos.nodes_searched() > next_checkmate
                && elapsed_time()+1000
                < std::max(Limits.maxTime,TimeMgr.maximum_time())*4/5) {
            run_checkmate(depth, next_checkmate, pos);
            next_checkmate *= 2;
            if (RootMoves[0].score <= VALUE_MATED_IN_PLY_MAX) {
                depth -= std::min(4, (int)depth/2);
                alpha = std::max(alpha - delta*63, -VALUE_INFINITE);
                beta  = std::min(beta  + delta*63,  VALUE_INFINITE);
            }
        }
#endif

        // MultiPV loop. We perform a full root search for each PV line
        for (MultiPVIdx = 0; MultiPVIdx < std::min(MultiPV, RootMoves.size()); MultiPVIdx++)
        {
            // Calculate dynamic aspiration window based on previous iteration
            if (depth >= 5 && abs(RootMoves[MultiPVIdx].score) < VALUE_KNOWN_WIN)
            {
                delta = abs(RootMoves[MultiPVIdx].score - RootMoves[MultiPVIdx].prevScore);
                delta = std::min(std::max(delta, 16), 24);
                delta = (delta + 7) / 8 * 8; // Round to match grainSize

                alpha = RootMoves[MultiPVIdx].score - delta;
                beta  = RootMoves[MultiPVIdx].score + delta;

                assert(alpha > -VALUE_INFINITE && beta < VALUE_INFINITE);
            }
            else
            {
                alpha = -VALUE_INFINITE;
                beta  =  VALUE_INFINITE;
            }

            // Start with a small aspiration window and, in case of fail high/low,
            // research with bigger window until not failing high/low anymore.
            do {
                // Search starts from ss+1 to allow referencing (ss-1). This is
                // needed by update gains and ss copy when splitting at Root.
                bestValue = search<Root>(pos, ss+1, alpha, beta, depth * ONE_PLY);

                // Bring to front the best move. It is critical that sorting is
                // done with a stable algorithm because all the values but the first
                // and eventually the new best one are set to -VALUE_INFINITE and
                // we want to keep the same order for all the moves but the new
                // PV that goes to the front. Note that in case of MultiPV search
                // the already searched PV lines are preserved.
                sort<RootMove>(RootMoves.begin() + MultiPVIdx, RootMoves.end());

                // In case we have found an exact score and we are going to leave
                // the fail high/low loop then reorder the PV moves, otherwise
                // leave the last PV move in its position so to be searched again.
                // Of course this is needed only in MultiPV search.
                if (MultiPVIdx && bestValue > alpha && bestValue < beta)
                    sort<RootMove>(RootMoves.begin(), RootMoves.begin() + MultiPVIdx);

                // Write PV back to transposition table in case the relevant entries
                // have been overwritten during the search.
                for (size_t i = 0; i <= MultiPVIdx; i++)
                    RootMoves[i].insert_pv_in_tt(pos);

                // If search has been stopped exit the aspiration window loop,
                // note that sorting and writing PV back to TT is safe becuase
                // Rml is still valid, although refers to the previous iteration.
                if (Signals.stop)
                    break;

                // Send full PV info to GUI if we are going to leave the loop or
                // if we have a fail high/low and we are deep in the search. UCI
                // protocol requires to send all the PV lines also if are still
                // to be searched and so refer to the previous search's score.
                if ((bestValue > alpha && bestValue < beta) || elapsed_time() > 2000)
                    for (size_t i = 0; i < std::min(UCIMultiPV, RootMoves.size()); i++)
                    {
                        bool updated = (i <= MultiPVIdx);

                        if (depth == 1 && !updated)
                            continue;

                        Depth d = (updated ? depth : depth - 1) * ONE_PLY;
                        Value s = (updated ? RootMoves[i].score : RootMoves[i].prevScore);

                        cout << "info"
                             << depth_to_uci(d)
                             << (i == MultiPVIdx ? score_to_uci(s, alpha, beta) : score_to_uci(s))
                             << speed_to_uci(pos.nodes_searched())
                             << pv_to_uci(&RootMoves[i].pv[0], i + 1, pos.is_chess960())
                             << endl;
                    }

                // In case of failing high/low increase aspiration window and
                // research, otherwise exit the fail high/low loop.
                if (bestValue >= beta)
                {
                    beta = std::min(beta + delta, VALUE_INFINITE);
                    delta += delta / 2;
                }
                else if (bestValue <= alpha)
                {
                    Signals.failedLowAtRoot = true;
                    Signals.stopOnPonderhit = false;

                    alpha = std::max(alpha - delta, -VALUE_INFINITE);
                    delta += delta / 2;
                }
                else
                    break;

            } while (abs(bestValue) < VALUE_KNOWN_WIN);
        }

        bestMove = RootMoves[0].pv[0];
        *ponderMove = RootMoves[0].pv[1];
        bestMoveChanges[depth] = BestMoveChanges;

        // Skills: Do we need to pick now the best and the ponder moves ?
        if (SkillLevelEnabled && depth == 1 + SkillLevel)
            do_skill_level(&skillBest, &skillPonder);

        if (Options["Use Search Log"].value<bool>())
        {
            Log log(Options["Search Log Filename"].value<string>());
            log << pretty_pv(pos, depth, bestValue, elapsed_time(), &RootMoves[0].pv[0]) << endl;
        }

        // Filter out startup noise when monitoring best move stability
        if (depth > 2 && bestMoveChanges[depth])
            bestMoveNeverChanged = false;

#if 0 //def GPSFISH
        // removed a6fc3d6ee501911375b29ebdb09638eb6789d091
        if (! Limits.ponder
          && !Signals.stop
          && depth >= 5
          && abs(bestValues[depth])     >= VALUE_MATE_IN_PLY_MAX
          && abs(bestValues[depth - 1]) >= VALUE_MATE_IN_PLY_MAX)
        {
            Signals.stop = true;
        }
#endif

        // Do we have time for the next iteration? Can we stop searching now?
        if (!Signals.stop && !Signals.stopOnPonderhit && Limits.useTimeManagement())
        {
            bool stop = false; // Local variable instead of the volatile Signals.stop

            // Take in account some extra time if the best move has changed
            if (depth > 4 && depth < 50)
                TimeMgr.pv_instability(bestMoveChanges[depth], bestMoveChanges[depth - 1]);

            // Stop search if most of available time is already consumed. We probably don't
            // have enough time to search the first move at the next iteration anyway.
            if (elapsed_time() > (TimeMgr.available_time() * 62) / 100)
                stop = true;

            // Stop search early if one move seems to be much better than others
            if (   depth >= 10
                && !stop
                && (   bestMoveNeverChanged
                    || elapsed_time() > (TimeMgr.available_time() * 40) / 100))
            {
                Value rBeta = bestValue - EasyMoveMargin;
                (ss+1)->excludedMove = bestMove;
                (ss+1)->skipNullMove = true;
                Value v = search<NonPV>(pos, ss+1, rBeta - 1, rBeta, (depth * ONE_PLY) / 2);
                (ss+1)->skipNullMove = false;
                (ss+1)->excludedMove = MOVE_NONE;

                if (v < rBeta)
                    stop = true;
            }

            if (stop)
            {
                // If we are allowed to ponder do not stop the search now but
                // keep pondering until GUI sends "ponderhit" or "stop".
                if (Limits.ponder)
                    Signals.stopOnPonderhit = true;
                else
                    Signals.stop = true;
            }
        }
    }

    // When using skills overwrite best and ponder moves with the sub-optimal ones
    if (SkillLevelEnabled)
    {
        if (skillBest == MOVE_NONE) // Still unassigned ?
            do_skill_level(&skillBest, &skillPonder);

        bestMove = skillBest;
        *ponderMove = skillPonder;
    }

    return bestMove;
  }

  // search<>() is the main search function for both PV and non-PV nodes and for
  // normal and SplitPoint nodes. When called just after a split point the search
  // is simpler because we have already probed the hash table, done a null move
  // search, and searched the first move before splitting, we don't have to repeat
  // all this work again. We also don't need to store anything to the hash table
  // here: This is taken care of after we return from the split point.

  template <NodeType NT>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth) {

    const bool PvNode   = (NT == PV || NT == Root || NT == SplitPointPV || NT == SplitPointRoot);
    const bool SpNode   = (NT == SplitPointPV || NT == SplitPointNonPV || NT == SplitPointRoot);
    const bool RootNode = (NT == Root || NT == SplitPointRoot);

    assert(alpha >= -VALUE_INFINITE && alpha <= VALUE_INFINITE);
    assert(beta > alpha && beta <= VALUE_INFINITE);
    assert(PvNode || alpha == beta - 1);
    assert(pos.thread() >= 0 && pos.thread() < Threads.size());

    Move movesSearched[MAX_MOVES];
    int64_t nodes;
    StateInfo st;
    const TTEntry *tte;
    Key posKey;
    Move ttMove, move, excludedMove, threatMove;
    Depth ext, newDepth;
    ValueType vt;
    Value bestValue, value, oldAlpha;
    Value refinedValue, nullValue, futilityBase, futilityValue;
    bool isPvMove, inCheck, singularExtensionNode, givesCheck;
    bool captureOrPromotion, dangerous, doFullDepthSearch;
    int moveCount = 0, playedMoveCount = 0;
    Thread& thread = Threads[pos.thread()];
    SplitPoint* sp = NULL;
#ifdef GPSFISH
    int repeat_check=0;
#endif

#ifdef GPSFISH
    if(can_capture_king(pos)){
      return value_mate_in(0);
    }
#endif
    refinedValue = bestValue = value = -VALUE_INFINITE;
    oldAlpha = alpha;
    inCheck = pos.in_check();
    ss->ply = (ss-1)->ply + 1;

    // Used to send selDepth info to GUI
    if (PvNode && thread.maxPly < ss->ply)
        thread.maxPly = ss->ply;

    // Step 1. Initialize node
    if (!SpNode)
    {
        ss->currentMove = ss->bestMove = threatMove = (ss+1)->excludedMove = MOVE_NONE;
        (ss+1)->skipNullMove = false; (ss+1)->reduction = DEPTH_ZERO;
        (ss+2)->killers[0] = (ss+2)->killers[1] = MOVE_NONE;
    }
    else
    {
        sp = ss->sp;
        tte = NULL;
        ttMove = excludedMove = MOVE_NONE;
        threatMove = sp->threatMove;
        goto split_point_start;
    }

    // Check for an instant draw or maximum ply reached
#ifdef GPSFISH
    if (Signals.stop || ss->ply > PLY_MAX || pos.is_draw(repeat_check))
        return value_draw(pos);

    if(repeat_check<0) 
        return value_mated_in(ss->ply+1);
    else if(repeat_check>0) 
        return value_mate_in(ss->ply);
#endif
    // Step 2. Check for aborted search and immediate draw
    if ((   Signals.stop
         || pos.is_draw<false>()
         || ss->ply > PLY_MAX) && !RootNode)
        return VALUE_DRAW;

#ifdef GPSFISH
    if ( !Root ){
        if(repeat_check<0) 
            return value_mated_in(ss->ply);
        else if(repeat_check>0) 
            return value_mate_in(ss->ply);
        else if(osl::EnterKing::canDeclareWin(pos.osl_state)) 
            return value_mate_in(ss->ply+1);
    }
    if (!ss->checkmateTested) {
        ss->checkmateTested = true;
        if(!pos.osl_state.inCheck()
                && ImmediateCheckmate::hasCheckmateMove
                (pos.side_to_move(),pos.osl_state,ss->bestMove)) {
            return value_mate_in(ss->ply);
        }
#  ifdef GPSFISH_CHECKMATE3
        if ((! (ss-1)->currentMove.isNormal()
                    || (ss-1)->currentMove.ptype() == osl::KING)) {
            osl::checkmate::King8Info king8=pos.osl_state.king8Info(alt(pos.side_to_move()));
            assert(king8.uint64Value() == osl::checkmate::King8Info::make(pos.side_to_move(), pos.osl_state).uint64Value());
            bool in_danger = king8.dropCandidate() | king8.moveCandidate2();
            if (in_danger) {
                osl::checkmate::FixedDepthSearcher solver(pos.osl_state);
                if (solver.hasCheckmateMoveOfTurn(2,ss->bestMove)
                        .isCheckmateSuccess()) {
                    return value_mate_in(ss->ply+2);;
                }
            }
        }
#  endif
    }
#endif

    // Step 3. Mate distance pruning
    if (!RootNode)
    {
        alpha = std::max(value_mated_in(ss->ply), alpha);
        beta = std::min(value_mate_in(ss->ply+1), beta);
        if (alpha >= beta)
            return alpha;
    }

    // Step 4. Transposition table lookup
    // We don't want the score of a partial search to overwrite a previous full search
    // TT value, so we use a different position key in case of an excluded move.
    excludedMove = ss->excludedMove;
#ifdef GPSFISH
    posKey = excludedMove!=MOVE_NONE ? pos.get_exclusion_key() : pos.get_key();
#else
    posKey = excludedMove ? pos.get_exclusion_key() : pos.get_key();
#endif

    tte = TT.probe(posKey);
#ifdef GPSFISH
    ttMove = RootNode ? RootMoves[MultiPVIdx].pv[0] : tte ? tte->move(pos) : MOVE_NONE;
#else
    ttMove = RootNode ? RootMoves[MultiPVIdx].pv[0] : tte ? tte->move() : MOVE_NONE;
#endif

    // At PV nodes we check for exact scores, while at non-PV nodes we check for
    // a fail high/low. Biggest advantage at probing at PV nodes is to have a
    // smooth experience in analysis mode. We don't probe at Root nodes otherwise
    // we should also update RootMoveList to avoid bogus output.
    if (!RootNode && tte && (PvNode ? tte->depth() >= depth && tte->type() == VALUE_TYPE_EXACT
                                    : can_return_tt(tte, depth, beta, ss->ply)))
    {
        TT.refresh(tte);
        ss->bestMove = move = ttMove; // Can be MOVE_NONE
        value = value_from_tt(tte->value(), ss->ply);

        if (   value >= beta
            && move
            && !pos.is_capture_or_promotion(move)
            && move != ss->killers[0])
        {
            ss->killers[1] = ss->killers[0];
            ss->killers[0] = move;
        }
        return value;
    }

    // Step 5. Evaluate the position statically and update parent's gain statistics
    if (inCheck)
        ss->eval = ss->evalMargin = VALUE_NONE;
    else if (tte)
    {
        assert(tte->static_value() != VALUE_NONE);

        ss->eval = tte->static_value();
        ss->evalMargin = tte->static_value_margin();
        refinedValue = refine_eval(tte, ss->eval, ss->ply);
    }
    else
    {
        refinedValue = ss->eval = evaluate(pos, ss->evalMargin);
        TT.store(posKey, VALUE_NONE, VALUE_TYPE_NONE, DEPTH_NONE, MOVE_NONE, ss->eval, ss->evalMargin);
    }

    // Update gain for the parent non-capture move given the static position
    // evaluation before and after the move.
#ifdef GPSFISH
    if (   !(move = (ss-1)->currentMove).isPass()
#else
    if (   (move = (ss-1)->currentMove) != MOVE_NULL
#endif
        && (ss-1)->eval != VALUE_NONE
        && ss->eval != VALUE_NONE
        && pos.captured_piece_type() == PIECE_TYPE_NONE
        && !is_special(move))
    {
        Square to = move_to(move);
#ifdef GPSFISH
        //H.update_gain(m.ptypeO(), move_to(m), -(before + after));
        H.update_gain(move.ptypeO(), to, -(ss-1)->eval - ss->eval);
#else
        H.update_gain(pos.piece_on(to), to, -(ss-1)->eval - ss->eval);
#endif
    }

    // Step 6. Razoring (is omitted in PV nodes)
    if (   !PvNode
        &&  depth < RazorDepth
        && !inCheck
        &&  refinedValue + razor_margin(depth) < beta
        &&  ttMove == MOVE_NONE
        &&  abs(beta) < VALUE_MATE_IN_PLY_MAX
#ifndef GPSFISH
        && !pos.has_pawn_on_7th(pos.side_to_move())
#endif
      )
    {
        Value rbeta = beta - razor_margin(depth);
        Value v = qsearch<NonPV>(pos, ss, rbeta-1, rbeta, DEPTH_ZERO);
        if (v < rbeta)
            // Logically we should return (v + razor_margin(depth)), but
            // surprisingly this did slightly weaker in tests.
            return v;
    }

    // Step 7. Static null move pruning (is omitted in PV nodes)
    // We're betting that the opponent doesn't have a move that will reduce
    // the score by more than futility_margin(depth) if we do a null move.
    if (   !PvNode
        && !ss->skipNullMove
        &&  depth < RazorDepth
        && !inCheck
        &&  refinedValue - futility_margin(depth, 0) >= beta
        &&  abs(beta) < VALUE_MATE_IN_PLY_MAX
#ifndef GPSFISH
        &&  pos.non_pawn_material(pos.side_to_move())
#endif
	   )
        return refinedValue - futility_margin(depth, 0);

    // Step 8. Null move search with verification search (is omitted in PV nodes)
    if (   !PvNode
        && !ss->skipNullMove
        &&  depth > ONE_PLY
        && !inCheck
        &&  refinedValue >= beta
        &&  abs(beta) < VALUE_MATE_IN_PLY_MAX
#ifdef GPSFISH
      )
#else
        &&  pos.non_pawn_material(pos.side_to_move()))
#endif
    {
#ifdef GPSFISH
        ss->currentMove = Move::PASS(pos.side_to_move());
#else
        ss->currentMove = MOVE_NULL;
#endif

        // Null move dynamic reduction based on depth
        int R = 3 + (depth >= 5 * ONE_PLY ? depth / 8 : 0);

        // Null move dynamic reduction based on value
        if (refinedValue - PawnValueMidgame > beta)
            R++;

#ifdef GPSFISH
        pos.do_undo_null_move(st,
                [&](osl::Square){
                *(pos.eval+1)= *(pos.eval);
                pos.eval++;
                pos.eval->update(pos.osl_state,ss->currentMove);
#else
        pos.do_null_move<true>(st);
#endif
        (ss+1)->skipNullMove = true;
        nullValue = depth-R*ONE_PLY < ONE_PLY ? -qsearch<NonPV>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                              : - search<NonPV>(pos, ss+1, -beta, -alpha, depth-R*ONE_PLY);
        (ss+1)->skipNullMove = false;
#ifdef GPSFISH
	    --pos.eval;
	  }
	  );
#else
        pos.do_null_move<false>(st);
#endif

        if (nullValue >= beta)
        {
            // Do not return unproven mate scores
            if (nullValue >= VALUE_MATE_IN_PLY_MAX)
                nullValue = beta;

            if (depth < 6 * ONE_PLY)
                return nullValue;

            // Do verification search at high depths
            ss->skipNullMove = true;
            Value v = search<NonPV>(pos, ss, alpha, beta, depth-R*ONE_PLY);
            ss->skipNullMove = false;

            if (v >= beta)
                return nullValue;
        }
        else
        {
            // The null move failed low, which means that we may be faced with
            // some kind of threat. If the previous move was reduced, check if
            // the move that refuted the null move was somehow connected to the
            // move which was reduced. If a connection is found, return a fail
            // low score (which will cause the reduced move to fail high in the
            // parent node, which will trigger a re-search with full depth).
            threatMove = (ss+1)->bestMove;

            if (   depth < ThreatDepth
                && (ss-1)->reduction
                && threatMove != MOVE_NONE
                && connected_moves(pos, (ss-1)->currentMove, threatMove))
                return beta - 1;
        }
    }

    // Step 9. ProbCut (is omitted in PV nodes)
    // If we have a very good capture (i.e. SEE > seeValues[captured_piece_type])
    // and a reduced search returns a value much above beta, we can (almost) safely
    // prune the previous move.
    if (   !PvNode
        &&  depth >= RazorDepth + ONE_PLY
        && !inCheck
        && !ss->skipNullMove
        &&  excludedMove == MOVE_NONE
        &&  abs(beta) < VALUE_MATE_IN_PLY_MAX)
    {
        Value rbeta = beta + 200;
        Depth rdepth = depth - ONE_PLY - 3 * ONE_PLY;

        assert(rdepth >= ONE_PLY);

        MovePicker mp(pos, ttMove, H, pos.captured_piece_type());
        CheckInfo ci(pos);

        while ((move = mp.get_next_move()) != MOVE_NONE)
            if (pos.pl_move_is_legal(move, ci.pinned))
            {
#ifdef GPSFISH
                pos.do_undo_move(move,st,
                        [&](osl::Square){
                        assert(pos.is_ok());
                        *(pos.eval+1)= *(pos.eval);
                        pos.eval++;
                        pos.eval->update(pos.osl_state,move);
#else
                pos.do_move(move, st, ci, pos.move_gives_check(move, ci));
#endif
                value = -search<NonPV>(pos, ss+1, -rbeta, -rbeta+1, rdepth);
#ifdef GPSFISH
                --pos.eval;
                });
#else
=======
                pos.undo_move(move);
#endif
                if (value >= rbeta)
                    return value;
            }
    }

    // Step 10. Internal iterative deepening
    if (   depth >= IIDDepth[PvNode]
        && ttMove == MOVE_NONE
        && (PvNode || (!inCheck && ss->eval + IIDMargin >= beta)))
    {
        Depth d = (PvNode ? depth - 2 * ONE_PLY : depth / 2);

        ss->skipNullMove = true;
        search<PvNode ? PV : NonPV>(pos, ss, alpha, beta, d);
        ss->skipNullMove = false;

        tte = TT.probe(posKey);
#ifdef GPSFISH
        ttMove = tte ? tte->move(pos) : MOVE_NONE;
#else
        ttMove = tte ? tte->move() : MOVE_NONE;
#endif
    }

split_point_start: // At split points actual search starts from here

    MovePickerExt<SpNode> mp(pos, ttMove, depth, H, ss, PvNode ? -VALUE_INFINITE : beta);
    CheckInfo ci(pos);
    ss->bestMove = MOVE_NONE;
    futilityBase = ss->eval + ss->evalMargin;
    singularExtensionNode =   !RootNode
                           && !SpNode
                           && depth >= SingularExtensionDepth[PvNode]
                           && ttMove != MOVE_NONE
#ifdef GPSFISH
                           && excludedMove==MOVE_NONE // Recursive singular search is not allowed
#else
                           && !excludedMove // Recursive singular search is not allowed
#endif
                           && (tte->type() & VALUE_TYPE_LOWER)
                           && tte->depth() >= depth - 3 * ONE_PLY;
    if (SpNode)
    {
        lock_grab(&(sp->lock));
        bestValue = sp->bestValue;
        moveCount = sp->moveCount;

        assert(bestValue > -VALUE_INFINITE && moveCount > 0);
    }

    // Step 11. Loop through moves
    // Loop through all pseudo-legal moves until no moves remain or a beta cutoff occurs
    while (   bestValue < beta
           && (move = mp.get_next_move()) != MOVE_NONE
           && !thread.cutoff_occurred())
    {
      assert(is_ok(move));

      if (move == excludedMove)
          continue;

      // At root obey the "searchmoves" option and skip moves not listed in Root
      // Move List, as a consequence any illegal move is also skipped. In MultiPV
      // mode we also skip PV moves which have been already searched.
      if (RootNode && !std::count(RootMoves.begin() + MultiPVIdx, RootMoves.end(), move))
          continue;

      // At PV and SpNode nodes we want all moves to be legal since the beginning
      if ((PvNode || SpNode) && !pos.pl_move_is_legal(move, ci.pinned))
          continue;

      if (SpNode)
      {
          moveCount = ++sp->moveCount;
          lock_release(&(sp->lock));
      }
      else
          moveCount++;
#ifdef MOVE_STACK_REJECTIONS
      if(!Root && move_stack_rejections_probe(move,pos,ss,alpha)) {
	if (SpNode)
	  lock_grab(&(sp->lock));
	continue;
      }
#endif      

      if (RootNode)
      {
          // This is used by time management
          Signals.firstRootMove = (moveCount == 1);

          nodes = pos.nodes_searched();

#ifndef GPSFISH
          if (pos.thread() == 0 && elapsed_time() > 2000)
              cout << "info" << depth_to_uci(depth)
                   << " currmove " << move
                   << " currmovenumber " << moveCount + MultiPVIdx << endl;
#endif
      }

      isPvMove = (PvNode && moveCount <= 1);
      captureOrPromotion = pos.is_capture_or_promotion(move);
      givesCheck = pos.move_gives_check(move, ci);
      dangerous = givesCheck || is_dangerous(pos, move, captureOrPromotion);
      ext = DEPTH_ZERO;

      // Step 12. Extend checks and, in PV nodes, also dangerous moves
      if (PvNode && dangerous)
          ext = ONE_PLY;

      else if (givesCheck && pos.see_sign(move) >= 0)
          ext = PvNode ? ONE_PLY : ONE_PLY / 2;

      // Singular extension search. If all moves but one fail low on a search of
      // (alpha-s, beta-s), and just one fails high on (alpha, beta), then that move
      // is singular and should be extended. To verify this we do a reduced search
      // on all the other moves but the ttMove, if result is lower than ttValue minus
      // a margin then we extend ttMove.
      if (   singularExtensionNode
          && !ext
          && move == ttMove
          && pos.pl_move_is_legal(move, ci.pinned))
      {
          Value ttValue = value_from_tt(tte->value(), ss->ply);

          if (abs(ttValue) < VALUE_KNOWN_WIN)
          {
              Value rBeta = ttValue - int(depth);
              ss->excludedMove = move;
              ss->skipNullMove = true;
              value = search<NonPV>(pos, ss, rBeta - 1, rBeta, depth / 2);
              ss->skipNullMove = false;
              ss->excludedMove = MOVE_NONE;
              ss->bestMove = MOVE_NONE;
              if (value < rBeta)
                  ext = ONE_PLY;
          }
      }

      // Update current move (this must be done after singular extension search)
      newDepth = depth - ONE_PLY + ext;

      // Step 13. Futility pruning (is omitted in PV nodes)
      if (   !PvNode
          && !captureOrPromotion
          && !inCheck
          && !dangerous
          &&  move != ttMove
          && !is_castle(move)
          && (bestValue > VALUE_MATED_IN_PLY_MAX || bestValue == -VALUE_INFINITE))
      {
          // Move count based pruning
          if (   moveCount >= futility_move_count(depth)
#ifdef GPSFISH
              && (threatMove==MOVE_NONE || !connected_threat(pos, move, threatMove)))
#else
              && (!threatMove || !connected_threat(pos, move, threatMove)))
#endif
          {
              if (SpNode)
                  lock_grab(&(sp->lock));

              continue;
          }

          // Value based pruning
          // We illogically ignore reduction condition depth >= 3*ONE_PLY for predicted depth,
          // but fixing this made program slightly weaker.
          Depth predictedDepth = newDepth - reduction<PvNode>(depth, moveCount);
          futilityValue =  futilityBase + futility_margin(predictedDepth, moveCount)
#ifdef GPSFISH
                         + H.gain(move.ptypeO(), move_to(move));
#else
                         + H.gain(pos.piece_on(move_from(move)), move_to(move));
#endif

          if (futilityValue < beta)
          {
              if (SpNode)
                  lock_grab(&(sp->lock));

              continue;
          }

          // Prune moves with negative SEE at low depths
          if (   predictedDepth < 2 * ONE_PLY
              && pos.see_sign(move) < 0)
          {
              if (SpNode)
                  lock_grab(&(sp->lock));

              continue;
          }
      }

      // Check for legality only before to do the move
      if (!pos.pl_move_is_legal(move, ci.pinned))
      {
          moveCount--;
          continue;
      }

      ss->currentMove = move;
      if (!SpNode && !captureOrPromotion)
          movesSearched[playedMoveCount++] = move;

#ifdef GPSFISH
      assert(pos.eval->value()==eval_t(pos.osl_state,false).value());
      (ss+1)->checkmateTested = false;
      pos.do_undo_move(move,st,
              [&](osl::Square){
              *(pos.eval+1)= *(pos.eval);
              pos.eval++;
              pos.eval->update(pos.osl_state,move);
              assert(pos.eval->value()==eval_t(pos.osl_state,false).value());

    const bool PvNode   = (NT == PV || NT == Root || NT == SplitPointPV || NT == SplitPointRoot);
    const bool SpNode   = (NT == SplitPointPV || NT == SplitPointNonPV || NT == SplitPointRoot);
    const bool RootNode = (NT == Root || NT == SplitPointRoot);

#else
      // Step 14. Make the move
      pos.do_move(move, st, ci, givesCheck);
#endif

      // Step 15. Reduced depth search (LMR). If the move fails high will be
      // re-searched at full depth.
      if (   depth > 3 * ONE_PLY
          && !isPvMove
          && !captureOrPromotion
          && !dangerous
          && !is_castle(move)
          &&  ss->killers[0] != move
          &&  ss->killers[1] != move)
      {
          ss->reduction = reduction<PvNode>(depth, moveCount);
          Depth d = newDepth - ss->reduction;
          alpha = SpNode ? sp->alpha : alpha;

          value = d < ONE_PLY ? -qsearch<NonPV>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                              : - search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d);

          doFullDepthSearch = (value > alpha && ss->reduction != DEPTH_ZERO);
          ss->reduction = DEPTH_ZERO;
      }
      else
          doFullDepthSearch = !isPvMove;

      // Step 16. Full depth search, when LMR is skipped or fails high
      if (doFullDepthSearch)
      {
          alpha = SpNode ? sp->alpha : alpha;
          value = newDepth < ONE_PLY ? -qsearch<NonPV>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                                     : - search<NonPV>(pos, ss+1, -(alpha+1), -alpha, newDepth);
      }

      // Only for PV nodes do a full PV search on the first move or after a fail
      // high, in the latter case search only if value < beta, otherwise let the
      // parent node to fail low with value <= alpha and to try another move.
      if (PvNode && (isPvMove || (value > alpha && (RootNode || value < beta))))
          value = newDepth < ONE_PLY ? -qsearch<PV>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                     : - search<PV>(pos, ss+1, -beta, -alpha, newDepth);

#ifdef GPSFISH
      --pos.eval;
      } );
#else
      // Step 17. Undo move
      pos.undo_move(move);
#endif

      assert(value > -VALUE_INFINITE && value < VALUE_INFINITE);

      // Step 18. Check for new best move
      if (SpNode)
      {
          lock_grab(&(sp->lock));
          bestValue = sp->bestValue;
          alpha = sp->alpha;
      }

      // Finished searching the move. If StopRequest is true, the search
      // was aborted because the user interrupted the search or because we
      // ran out of time. In this case, the return value of the search cannot
      // be trusted, and we don't update the best move and/or PV.
      if (RootNode && !Signals.stop)
      {
          RootMove& rm = *std::find(RootMoves.begin(), RootMoves.end(), move);
          rm.nodes += pos.nodes_searched() - nodes;

          // PV move or new best move ?
          if (isPvMove || value > alpha)
          {
              rm.score = value;
              rm.extract_pv_from_tt(pos);

              // We record how often the best move has been changed in each
              // iteration. This information is used for time management: When
              // the best move changes frequently, we allocate some more time.
              if (!isPvMove && MultiPV == 1)
                  BestMoveChanges++;

#if 0 //def GPSFISH
              if (depth >= 5*ONE_PLY
                      && (!isPvMove || current_search_time() >= 5000))
                  cout << "info"
                      << depth_to_uci(depth)
                      << score_to_uci(rm->score, alpha, beta)
                      << speed_to_uci(pos.nodes_searched())
                      << pv_to_uci(&rm->pv[0], 0 + 1, false) << endl;
#endif

          }
          else
              // All other moves but the PV are set to the lowest value, this
              // is not a problem when sorting becuase sort is stable and move
              // position in the list is preserved, just the PV is pushed up.
              rm.score = -VALUE_INFINITE;

      }

      if (value > bestValue)
      {
          bestValue = value;
          ss->bestMove = move;

          if (   PvNode
              && value > alpha
              && value < beta) // We want always alpha < beta
              alpha = value;

          if (SpNode && !thread.cutoff_occurred())
          {
              sp->bestValue = value;
              sp->ss->bestMove = move;
              sp->alpha = alpha;
              sp->is_betaCutoff = (value >= beta);
          }
      }

      // Step 19. Check for split
      if (   !SpNode
          && depth >= Threads.min_split_depth()
          && bestValue < beta
          && Threads.available_slave_exists(pos.thread())
          && !Signals.stop
          && !thread.cutoff_occurred())
          bestValue = Threads.split<FakeSplit>(pos, ss, alpha, beta, bestValue, depth,
                                               threatMove, moveCount, &mp, NT);
    }

    // Step 20. Check for mate and stalemate
    // All legal moves have been searched and if there are no legal moves, it
    // must be mate or stalemate. Note that we can have a false positive in
    // case of StopRequest or thread.cutoff_occurred() are set, but this is
    // harmless because return value is discarded anyhow in the parent nodes.
    // If we are in a singular extension search then return a fail low score.
    if (!moveCount)
#ifdef GPSFISH
        return excludedMove!=MOVE_NONE ? oldAlpha : (inCheck ? (move_is_pawn_drop((ss-1)->currentMove) ? value_mate_in(ss->ply) : value_mated_in(ss->ply) ): VALUE_DRAW);
#else
        return excludedMove ? oldAlpha : inCheck ? value_mated_in(ss->ply) : VALUE_DRAW;
#endif

    // If we have pruned all the moves without searching return a fail-low score
    if (bestValue == -VALUE_INFINITE)
    {
        assert(!playedMoveCount);

        bestValue = alpha;
    }

    // Step 21. Update tables
    // Update transposition table entry, history and killers
    if (!SpNode && !Signals.stop && !thread.cutoff_occurred())
    {
        move = bestValue <= oldAlpha ? MOVE_NONE : ss->bestMove;
        vt   = bestValue <= oldAlpha ? VALUE_TYPE_UPPER
             : bestValue >= beta ? VALUE_TYPE_LOWER : VALUE_TYPE_EXACT;

        TT.store(posKey, value_to_tt(bestValue, ss->ply), vt, depth, move, ss->eval, ss->evalMargin);

        // Update killers and history only for non capture moves that fails high
        if (    bestValue >= beta
            && !pos.is_capture_or_promotion(move))
        {
            if (move != ss->killers[0])
            {
                ss->killers[1] = ss->killers[0];
                ss->killers[0] = move;
            }
            update_history(pos, move, depth, movesSearched, playedMoveCount);
        }
    }

    if (SpNode)
    {
        // Here we have the lock still grabbed
        sp->is_slave[pos.thread()] = false;
        sp->nodes += pos.nodes_searched();
        lock_release(&(sp->lock));
    }

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // qsearch() is the quiescence search function, which is called by the main
  // search function when the remaining depth is zero (or, to be more precise,
  // less than ONE_PLY).

  template <NodeType NT>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth) {

    const bool PvNode = (NT == PV);

    assert(NT == PV || NT == NonPV);
    assert(alpha >= -VALUE_INFINITE && alpha <= VALUE_INFINITE);
    assert(beta >= -VALUE_INFINITE && beta <= VALUE_INFINITE);
    assert(PvNode || alpha == beta - 1);
    assert(depth <= 0);
    assert(pos.thread() >= 0 && pos.thread() < Threads.size());

    StateInfo st;
    Move ttMove, move;
    Value bestValue, value, evalMargin, futilityValue, futilityBase;
#ifdef GPSFISH
    bool inCheck, givesCheck, evasionPrunable;
#else
    bool inCheck, enoughMaterial, givesCheck, evasionPrunable;
#endif
    const TTEntry* tte;
    Depth ttDepth;
    ValueType vt;
    Value oldAlpha = alpha;

    ss->bestMove = ss->currentMove = MOVE_NONE;
    ss->ply = (ss-1)->ply + 1;

    // Check for an instant draw or maximum ply reached
    if (pos.is_draw<true>() || ss->ply > PLY_MAX)
        return VALUE_DRAW;

#ifdef GPSFISH
    if(can_capture_king(pos)){
        return value_mate_in(0);
    }
    if(!pos.osl_state.inCheck()
            && ImmediateCheckmate::hasCheckmateMove
            (pos.side_to_move(),pos.osl_state,ss->bestMove)) {
        return value_mate_in(ss->ply); 
    }
#endif

    // Decide whether or not to include checks, this fixes also the type of
    // TT entry depth that we are going to use. Note that in qsearch we use
    // only two types of depth in TT: DEPTH_QS_CHECKS or DEPTH_QS_NO_CHECKS.
    inCheck = pos.in_check();
    ttDepth = (inCheck || depth >= DEPTH_QS_CHECKS ? DEPTH_QS_CHECKS : DEPTH_QS_NO_CHECKS);

    // Transposition table lookup. At PV nodes, we don't use the TT for
    // pruning, but only for move ordering.
    tte = TT.probe(pos.get_key());
#ifdef GPSFISH
    ttMove = (tte ? tte->move(pos) : MOVE_NONE);
#else
    ttMove = (tte ? tte->move() : MOVE_NONE);
#endif

    if (!PvNode && tte && can_return_tt(tte, ttDepth, beta, ss->ply))
    {
        ss->bestMove = ttMove; // Can be MOVE_NONE
        return value_from_tt(tte->value(), ss->ply);
    }

    // Evaluate the position statically
    if (inCheck)
    {
        bestValue = futilityBase = -VALUE_INFINITE;
        ss->eval = evalMargin = VALUE_NONE;
#ifndef GPSFISH
        enoughMaterial = false;
#endif
    }
    else
    {
        if (tte)
        {
            assert(tte->static_value() != VALUE_NONE);

            evalMargin = tte->static_value_margin();
            ss->eval = bestValue = tte->static_value();
        }
        else
            ss->eval = bestValue = evaluate(pos, evalMargin);

        // Stand pat. Return immediately if static value is at least beta
        if (bestValue >= beta)
        {
            if (!tte)
                TT.store(pos.get_key(), value_to_tt(bestValue, ss->ply), VALUE_TYPE_LOWER, DEPTH_NONE, MOVE_NONE, ss->eval, evalMargin);

            return bestValue;
        }

        if (PvNode && bestValue > alpha)
            alpha = bestValue;

        futilityBase = ss->eval + evalMargin + FutilityMarginQS;
#ifndef GPSFISH
        enoughMaterial = pos.non_pawn_material(pos.side_to_move()) > RookValueMidgame;
#endif
    }

    // Initialize a MovePicker object for the current position, and prepare
    // to search the moves. Because the depth is <= 0 here, only captures,
    // queen promotions and checks (only if depth >= DEPTH_QS_CHECKS) will
    // be generated.
    MovePicker mp(pos, ttMove, depth, H, move_to((ss-1)->currentMove));
    CheckInfo ci(pos);

    // Loop through the moves until no moves remain or a beta cutoff occurs
    while (   bestValue < beta
           && (move = mp.get_next_move()) != MOVE_NONE)
    {
      assert(is_ok(move));

#ifdef MOVE_STACK_REJECTIONS
      if(move_stack_rejections_probe(move,pos,ss,alpha)) continue;
#endif      

      givesCheck = pos.move_gives_check(move, ci);

      // Futility pruning
      if (   !PvNode
          && !inCheck
          && !givesCheck
          &&  move != ttMove
#ifndef GPSFISH
          &&  enoughMaterial
          && !is_promotion(move)
          && !pos.is_passed_pawn_push(move))
#endif
         )
      {
#ifdef GPSFISH
          futilityValue =  futilityBase
                         + PieceValueEndgame[pos.piece_on(move_to(move))]
                         + (is_promotion(move) ? promote_value_of_piece_on(pos.piece_on(move_from(move))) : VALUE_ZERO);
#else
          futilityValue =  futilityBase
                         + PieceValueEndgame[pos.piece_on(move_to(move))]
                         + (is_enpassant(move) ? PawnValueEndgame : VALUE_ZERO);
#endif

          if (futilityValue < beta)
          {
              if (futilityValue > bestValue)
                  bestValue = futilityValue;

              continue;
          }

          // Prune moves with negative or equal SEE
          if (   futilityBase < beta
              && depth < DEPTH_ZERO
              && pos.see(move) <= 0)
              continue;
      }

      // Detect non-capture evasions that are candidate to be pruned
      evasionPrunable =   !PvNode
                       && inCheck
                       && bestValue > VALUE_MATED_IN_PLY_MAX
                       && !pos.is_capture(move)
#ifndef GPSFISH
                       && !pos.can_castle(pos.side_to_move())
#endif
                       ;

      // Don't search moves with negative SEE values
      if (   !PvNode
          && (!inCheck || evasionPrunable)
          &&  move != ttMove
#ifndef GPSFISH
          && !is_promotion(move)
#endif
          &&  pos.see_sign(move) < 0)
          continue;

      // Don't search useless checks
      if (   !PvNode
          && !inCheck
          &&  givesCheck
          &&  move != ttMove
          && !pos.is_capture_or_promotion(move)
          &&  ss->eval + PawnValueMidgame / 4 < beta
          && !check_is_dangerous(pos, move, futilityBase, beta, &bestValue))
      {
          if (ss->eval + PawnValueMidgame / 4 > bestValue)
              bestValue = ss->eval + PawnValueMidgame / 4;

          continue;
      }

      // Check for legality only before to do the move
      if (!pos.pl_move_is_legal(move, ci.pinned))
          continue;

      ss->currentMove = move;

      // Make and search the move
#ifdef GPSFISH
      pos.do_undo_move(move,st,
              [&](osl::Square){
              assert(pos.is_ok());
              *(pos.eval+1)= *(pos.eval);
              pos.eval++;
              pos.eval->update(pos.osl_state,move);
              assert(pos.eval_is_ok());
#else
      pos.do_move(move, st, ci, givesCheck);
#endif
      value = -qsearch<NT>(pos, ss+1, -beta, -alpha, depth-ONE_PLY);
#ifdef GPSFISH
      --pos.eval;
      }
      );
#else
      pos.undo_move(move);
#endif

      assert(value > -VALUE_INFINITE && value < VALUE_INFINITE);

      // New best move?
      if (value > bestValue)
      {
          bestValue = value;
          ss->bestMove = move;

          if (   PvNode
              && value > alpha
              && value < beta) // We want always alpha < beta
              alpha = value;
       }
    }

#ifdef GPSFISH_CHECKMATE3_QUIESCE
    if (bestValue < beta && depth >= DEPTH_QS_CHECKS
            && (!(ss-1)->currentMove.isNormal()
                || (ss-1)->currentMove.ptype() == osl::KING)) {
        osl::checkmate::King8Info king8=pos.osl_state.king8Info(alt(pos.side_to_move()));
        assert(king8.uint64Value() == osl::checkmate::King8Info::make(pos.side_to_move(), pos.osl_state).uint64Value());
        bool in_danger = king8.dropCandidate() | king8.moveCandidate2();
        if (in_danger) {
            osl::checkmate::FixedDepthSearcher solver(pos.osl_state);
            if (solver.hasCheckmateMoveOfTurn(2,(ss)->bestMove).isCheckmateSuccess()) {
                return value_mate_in(ss->ply+2);;
            }
        }
    }
#endif

    // All legal moves have been searched. A special case: If we're in check
    // and no legal moves were found, it is checkmate.
    if (inCheck && bestValue == -VALUE_INFINITE)
#ifdef GPSFISH
        return (move_is_pawn_drop((ss-1)->currentMove) ? value_mate_in(ss->ply) : value_mated_in(ss->ply));
#else
        return value_mated_in(ss->ply);
#endif

    // Update transposition table
    move = bestValue <= oldAlpha ? MOVE_NONE : ss->bestMove;
    vt   = bestValue <= oldAlpha ? VALUE_TYPE_UPPER
         : bestValue >= beta ? VALUE_TYPE_LOWER : VALUE_TYPE_EXACT;

    TT.store(pos.get_key(), value_to_tt(bestValue, ss->ply), vt, ttDepth, move, ss->eval, evalMargin);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // check_is_dangerous() tests if a checking move can be pruned in qsearch().
  // bestValue is updated only when returning false because in that case move
  // will be pruned.

  bool check_is_dangerous(Position &pos, Move move, Value futilityBase, Value beta, Value *bestValue)
  {
#ifdef GPSFISH
    return false;
#else
    Bitboard b, occ, oldAtt, newAtt, kingAtt;
    Square from, to, ksq, victimSq;
    Piece pc;
    Color them;
    Value futilityValue, bv = *bestValue;

    from = move_from(move);
    to = move_to(move);
    them = flip(pos.side_to_move());
    ksq = pos.king_square(them);
    kingAtt = pos.attacks_from<KING>(ksq);
    pc = pos.piece_on(from);

    occ = pos.occupied_squares() & ~(1ULL << from) & ~(1ULL << ksq);
    oldAtt = pos.attacks_from(pc, from, occ);
    newAtt = pos.attacks_from(pc,   to, occ);

    // Rule 1. Checks which give opponent's king at most one escape square are dangerous
    b = kingAtt & ~pos.pieces(them) & ~newAtt & ~(1ULL << to);

    if (!(b && (b & (b - 1))))
        return true;

    // Rule 2. Queen contact check is very dangerous
    if (   type_of(pc) == QUEEN
        && bit_is_set(kingAtt, to))
        return true;

    // Rule 3. Creating new double threats with checks
    b = pos.pieces(them) & newAtt & ~oldAtt & ~(1ULL << ksq);

    while (b)
    {
        victimSq = pop_1st_bit(&b);
        futilityValue = futilityBase + PieceValueEndgame[pos.piece_on(victimSq)];

        // Note that here we generate illegal "double move"!
        if (   futilityValue >= beta
            && pos.see_sign(make_move(from, victimSq)) >= 0)
            return true;

        if (futilityValue > bv)
            bv = futilityValue;
    }

    // Update bestValue only if check is not dangerous (because we will prune the move)
    *bestValue = bv;
    return false;
#endif
  }


  // connected_moves() tests whether two moves are 'connected' in the sense
  // that the first move somehow made the second move possible (for instance
  // if the moving piece is the same in both moves). The first move is assumed
  // to be the move that was made to reach the current position, while the
  // second move is assumed to be a move from the current position.

  bool connected_moves(const Position& pos, Move m1, Move m2) {

    Square f1, t1, f2, t2;
    Piece p1; //, p2;
    Square ksq;

    assert(is_ok(m1));
    assert(is_ok(m2));

    // Case 1: The moving piece is the same in both moves
    f2 = move_from(m2);
    t1 = move_to(m1);
    if (f2 == t1)
        return true;

    // Case 2: The destination square for m2 was vacated by m1
    t2 = move_to(m2);
    f1 = move_from(m1);
    if (t2 == f1)
        return true;

    // Case 3: Moving through the vacated square
#ifdef GPSFISH
    if(!f2.isPieceStand() && !f1.isPieceStand() &&
       Board_Table.getShortOffset(Offset32(f2,t2)) ==
       Board_Table.getShortOffset(Offset32(f2,f1)) &&
       abs((f2-t2).intValue())>abs((f2-f1).intValue())) return true;
#else
    p2 = pos.piece_on(f2);
    if (   piece_is_slider(p2)
        && bit_is_set(squares_between(f2, t2), f1))
      return true;
#endif

    // Case 4: The destination square for m2 is defended by the moving piece in m1
    p1 = pos.piece_on(t1);
#ifdef GPSFISH
    osl::Piece pc=pos.osl_state.pieceAt(t1);
    if(pos.osl_state.hasEffectByPiece(pc,t2)) return true;
#else
    if (bit_is_set(pos.attacks_from(p1, t1), t2))
        return true;
#endif

    // Case 5: Discovered check, checking piece is the piece moved in m1
#ifdef GPSFISH
    pc=pos.osl_state.pieceAt(t2);
    if(pc.isPiece() && pos.osl_state.hasEffectByPiece(pc,f2) &&
       Ptype_Table.getEffect(p1,t1,pos.king_square(pos.side_to_move())).hasBlockableEffect() &&
       Board_Table.isBetweenSafe(f2,t1,pos.king_square(pos.side_to_move())) &&
       !Board_Table.isBetweenSafe(t2,t1,pos.king_square(pos.side_to_move())) &&
       pos.osl_state.pinOrOpen(pos.side_to_move()).test(pos.osl_state.pieceAt(t1).number()))
        return true;
#else
    ksq = pos.king_square(pos.side_to_move());
    if (    piece_is_slider(p1)
        &&  bit_is_set(squares_between(t1, ksq), f2))
    {
        Bitboard occ = pos.occupied_squares();
        clear_bit(&occ, f2);
        if (bit_is_set(pos.attacks_from(p1, t1, occ), ksq))
            return true;
    }
#endif
    return false;
  }


  // value_to_tt() adjusts a mate score from "plies to mate from the root" to
  // "plies to mate from the current ply".  Non-mate scores are unchanged.
  // The function is called before storing a value to the transposition table.

  Value value_to_tt(Value v, int ply) {

    if (v >= VALUE_MATE_IN_PLY_MAX)
      return v + ply;

    if (v <= VALUE_MATED_IN_PLY_MAX)
      return v - ply;

    return v;
  }


  // value_from_tt() is the inverse of value_to_tt(): It adjusts a mate score from
  // the transposition table to a mate score corrected for the current ply.

  Value value_from_tt(Value v, int ply) {

    if (v >= VALUE_MATE_IN_PLY_MAX)
      return v - ply;

    if (v <= VALUE_MATED_IN_PLY_MAX)
      return v + ply;

    return v;
  }


  // connected_threat() tests whether it is safe to forward prune a move or if
  // is somehow connected to the threat move returned by null search.

  bool connected_threat(const Position& pos, Move m, Move threat) {

    assert(is_ok(m));
    assert(is_ok(threat));
    assert(!pos.is_capture_or_promotion(m));
#ifndef GPSFISH
    assert(!pos.is_passed_pawn_push(m));
#endif

    Square mfrom, mto, tfrom, tto;

    mfrom = move_from(m);
    mto = move_to(m);
    tfrom = move_from(threat);
    tto = move_to(threat);

    // Case 1: Don't prune moves which move the threatened piece
    if (mfrom == tto)
        return true;

    // Case 2: If the threatened piece has value less than or equal to the
    // value of the threatening piece, don't prune moves which defend it.
    if (   pos.is_capture(threat)
        && (   PieceValueMidgame[pos.piece_on(tfrom)] >= PieceValueMidgame[pos.piece_on(tto)]
#ifdef GPSFISH
            || type_of(pos.piece_on(tfrom)) == osl::KING)
#else
            || type_of(pos.piece_on(tfrom)) == KING)
#endif
        && pos.move_attacks_square(m, tto))
        return true;

    // Case 3: If the moving piece in the threatened move is a slider, don't
    // prune safe moves which block its ray.
#ifdef GPSFISH
    if (   !tfrom.isPieceStand()
        && Board_Table.isBetweenSafe(mto,tfrom,tto)
        && pos.see_sign(m) >= 0)
        return true;
#else
    if (   piece_is_slider(pos.piece_on(tfrom))
        && bit_is_set(squares_between(tfrom, tto), mto)
        && pos.see_sign(m) >= 0)
        return true;
#endif

    return false;
  }


  // can_return_tt() returns true if a transposition table score can be used to
  // cut-off at a given point in search.

  bool can_return_tt(const TTEntry* tte, Depth depth, Value beta, int ply) {

    Value v = value_from_tt(tte->value(), ply);

    return   (   tte->depth() >= depth
              || v >= std::max(VALUE_MATE_IN_PLY_MAX, beta)
              || v < std::min(VALUE_MATED_IN_PLY_MAX, beta))

          && (   ((tte->type() & VALUE_TYPE_LOWER) && v >= beta)
              || ((tte->type() & VALUE_TYPE_UPPER) && v < beta));
  }


  // refine_eval() returns the transposition table score if possible, otherwise
  // falls back on static position evaluation.

  Value refine_eval(const TTEntry* tte, Value defaultEval, int ply) {

      assert(tte);

      Value v = value_from_tt(tte->value(), ply);

      if (   ((tte->type() & VALUE_TYPE_LOWER) && v >= defaultEval)
          || ((tte->type() & VALUE_TYPE_UPPER) && v < defaultEval))
          return v;

      return defaultEval;
  }


  // update_history() registers a good move that produced a beta-cutoff in
  // history and marks as failures all the other moves of that ply.

  void update_history(const Position& pos, Move move, Depth depth,
                      Move movesSearched[], int moveCount) {
    Move m;
    Value bonus = Value(int(depth) * int(depth));

#ifdef GPSFISH
    H.update(move.ptypeO(), move_to(move), bonus);
#else
    H.update(pos.piece_on(move_from(move)), move_to(move), bonus);
#endif

    for (int i = 0; i < moveCount - 1; i++)
    {
        m = movesSearched[i];

        assert(m != move);

#ifdef GPSFISH
        H.update(m.ptypeO(), move_to(m), -bonus);
#else
        H.update(pos.piece_on(move_from(m)), move_to(m), -bonus);
#endif
    }
  }


  // current_search_time() returns the number of milliseconds which have passed
  // since the beginning of the current search.

  int elapsed_time(bool reset) {

    static int searchStartTime;

    if (reset)
        searchStartTime = get_system_time();

    return get_system_time() - searchStartTime;
  }


  // score_to_uci() converts a value to a string suitable for use with the UCI
  // protocol specifications:
  //
  // cp <x>     The score from the engine's point of view in centipawns.
  // mate <y>   Mate in y moves, not plies. If the engine is getting mated
  //            use negative values for y.

  string score_to_uci(Value v, Value alpha, Value beta) {

    std::stringstream s;

#ifdef GPSFISH
    if (abs(v) < VALUE_MATE - PLY_MAX * ONE_PLY)
        s << " score cp " << int(v) * 100 / 200;
    else
        s << " score mate " << int(v);
#else
    if (abs(v) < VALUE_MATE - PLY_MAX * ONE_PLY)
        s << " score cp " << int(v) * 100 / int(PawnValueMidgame); // Scale to centipawns
    else
        s << " score mate " << (v > 0 ? VALUE_MATE - v + 1 : -VALUE_MATE - v) / 2;

    s << (v >= beta ? " lowerbound" : v <= alpha ? " upperbound" : "");
#endif

    return s.str();
  }


  // speed_to_uci() returns a string with time stats of current search suitable
  // to be sent to UCI gui.

  string speed_to_uci(int64_t nodes) {

    std::stringstream s;
    int t = elapsed_time();

    s << " nodes " << nodes
      << " nps " << (t > 0 ? int(nodes * 1000 / t) : 0)
#ifdef GPSFISH
      << " time "  << (t > 0 ? t : 1);
#else
      << " time "  << t;
#endif

    return s.str();
  }


  // pv_to_uci() returns a string with information on the current PV line
  // formatted according to UCI specification.

  string pv_to_uci(const Move pv[], int pvNum, bool chess960) {

    std::stringstream s;

#ifdef GPSFISH
    s << " pv ";
#else
    s << " multipv " << pvNum << " pv " << set960(chess960);
#endif

    for ( ; *pv != MOVE_NONE; pv++)
#ifdef GPSFISH
        s << move_to_uci(*pv,false) << " ";
#else
        s << *pv << " ";
#endif

    return s.str();
  }


  // depth_to_uci() returns a string with information on the current depth and
  // seldepth formatted according to UCI specification.

  string depth_to_uci(Depth depth) {

    std::stringstream s;
    int selDepth = 0;

    // Retrieve max searched depth among threads
    for (int i = 0; i < Threads.size(); i++)
        if (Threads[i].maxPly > selDepth)
            selDepth = Threads[i].maxPly;

    s << " depth " << depth / ONE_PLY << " seldepth " << selDepth;

    return s.str();
  }


  // pretty_pv() creates a human-readable string from a position and a PV. It is
  // used to write search information to the log file (which is created when the
  // UCI parameter "Use Search Log" is "true"). It uses the two below helper to
  // pretty format time and score respectively.

  string time_to_string(int millisecs) {

    const int MSecMinute = 1000 * 60;
    const int MSecHour   = 1000 * 60 * 60;

    int hours = millisecs / MSecHour;
    int minutes =  (millisecs % MSecHour) / MSecMinute;
    int seconds = ((millisecs % MSecHour) % MSecMinute) / 1000;

    std::stringstream s;

    if (hours)
        s << hours << ':';

    s << std::setfill('0') << std::setw(2) << minutes << ':'
                           << std::setw(2) << seconds;
    return s.str();
  }

  string score_to_string(Value v) {

    std::stringstream s;

    if (v >= VALUE_MATE_IN_PLY_MAX)
        s << "#" << (VALUE_MATE - v + 1) / 2;
    else if (v <= VALUE_MATED_IN_PLY_MAX)
        s << "-#" << (VALUE_MATE + v) / 2;
    else
        s << std::setprecision(2) << std::fixed << std::showpos
          << float(v) / PawnValueMidgame;

    return s.str();
  }

  string pretty_pv(Position& pos, int depth, Value value, int time, Move pv[]) {

    const int64_t K = 1000;
    const int64_t M = 1000000;

    StateInfo state[PLY_MAX_PLUS_2], *st = state;
    Move* m = pv;
    string san, padding;
    size_t length;
    std::stringstream s;

#ifdef GPSFISH
    s
#else
    s << set960(pos.is_chess960())
#endif
      << std::setw(2) << depth
      << std::setw(8) << score_to_string(value)
      << std::setw(8) << time_to_string(time);

    if (pos.nodes_searched() < M)
        s << std::setw(8) << pos.nodes_searched() / 1 << "  ";
    else if (pos.nodes_searched() < K * M)
        s << std::setw(7) << pos.nodes_searched() / K << "K  ";
    else
        s << std::setw(7) << pos.nodes_searched() / M << "M  ";

    padding = string(s.str().length(), ' ');
    length = padding.length();

    while (*m != MOVE_NONE)
    {
        san = move_to_san(pos, *m);

        if (length + san.length() > 80)
        {
            s << "\n" + padding;
            length = padding.length();
        }

        s << san << ' ';
        length += san.length() + 1;

        pos.do_move(*m++, *st++);
    }

    // Restore original position before to leave
#ifndef GPSFISH
    while (m != pv)
        pos.undo_move(*--m);
#endif

    return s.str();
  }


  // When playing with strength handicap choose best move among the MultiPV set
  // using a statistical rule dependent on SkillLevel. Idea by Heinz van Saanen.

  void do_skill_level(Move* best, Move* ponder) {

    assert(MultiPV > 1);

    static RKISS rk;

    // PRNG sequence should be not deterministic
    for (int i = abs(get_system_time() % 50); i > 0; i--)
        rk.rand<unsigned>();

    // Rml list is already sorted by score in descending order
    size_t size = std::min(MultiPV, RootMoves.size());
    int variance = std::min(RootMoves[0].score - RootMoves[size - 1].score, PawnValueMidgame);
    int weakness = 120 - 2 * SkillLevel;
    int max_s = -VALUE_INFINITE;

    // Choose best move. For each move score we add two terms both dependent on
    // weakness, one deterministic and bigger for weaker moves, and one random,
    // then we choose the move with the resulting highest score.
    for (size_t i = 0; i < size; i++)
    {
        int s = RootMoves[i].score;

        // Don't allow crazy blunders even at very low skills
        if (i > 0 && RootMoves[i-1].score > s + EasyMoveMargin)
            break;

        // This is our magic formula
        s += (  weakness * int(RootMoves[0].score - s)
              + variance * (rk.rand<unsigned>() % weakness)) / 128;

        if (s > max_s)
        {
            max_s = s;
            *best = RootMoves[i].pv[0];
            *ponder = RootMoves[i].pv[1];
        }
    }
  }


#ifdef GPSFISH
  void RootMove::extract_pv_from_tt_rec(Position& pos,int ply) {
    TTEntry* tte;

    if (   (tte = TT.probe(pos.get_key())) != NULL
           && tte->move(pos) != MOVE_NONE
           && pos.is_pseudo_legal(tte->move(pos))
           && pos.pl_move_is_legal(tte->move(pos), pos.pinned_pieces())
           && ply < PLY_MAX
           && (!pos.is_draw<false>() || ply < 2))
    {
        pv.push_back(tte->move(pos));
        StateInfo st;
        pos.do_undo_move(tte->move(pos),st,
                [&](osl::Square){
                assert(pos.is_ok());
                extract_pv_from_tt_rec(pos,ply+1);
                }
                );
    }

    pv.push_back(MOVE_NONE);
  }
#endif

  // extract_pv_from_tt() builds a PV by adding moves from the transposition table.
  // We consider also failing high nodes and not only VALUE_TYPE_EXACT nodes. This
  // allow to always have a ponder move even when we fail high at root and also a
  // long PV to print that is important for position analysis.

  void RootMove::extract_pv_from_tt(Position& pos) {

#ifndef GPSFISH
    StateInfo state[PLY_MAX_PLUS_2], *st = state;
    TTEntry* tte;
    int ply = 1;
#endif
    Move m = pv[0];

    assert(m != MOVE_NONE && pos.is_pseudo_legal(m));

    pv.clear();
    pv.push_back(m);

#ifdef GPSFISH
    StateInfo st;
    pos.do_undo_move(pv[0],st,
		     [&](osl::Square){
         assert(pos.is_ok());
         extract_pv_from_tt_rec(pos,1);
         }
         );
#else
    pos.do_move(m, *st++);

    while (   (tte = TT.probe(pos.get_key())) != NULL
           && tte->move() != MOVE_NONE
           && pos.is_pseudo_legal(tte->move())
           && pos.pl_move_is_legal(tte->move(), pos.pinned_pieces())
           && ply < PLY_MAX
           && (!pos.is_draw<false>() || ply < 2))
    {
        pv.push_back(tte->move());
        pos.do_move(tte->move(), *st++);
        ply++;
    }
    pv.push_back(MOVE_NONE);

    do pos.undo_move(pv[--ply]); while (ply);
#endif
  }

#ifdef GPSFISH
  void RootMove::insert_pv_in_tt_rec(Position& pos,int ply) {
    TTEntry* tte;
    Key k;
    Value v, m = VALUE_NONE;
    k = pos.get_key();
    tte = TT.probe(k);

    // Don't overwrite existing correct entries
    if (!tte || tte->move(pos) != pv[ply])
    {
      v = (pos.in_check() ? VALUE_NONE : evaluate(pos, m));
      TT.store(k, VALUE_NONE, VALUE_TYPE_NONE, DEPTH_NONE, pv[ply], v, m);
    }
    if(pv[ply+1]!=MOVE_NONE){
        StateInfo st;
        pos.do_undo_move(pv[ply],st,
		       [&](osl::Square){
           assert(pos.is_ok());
           *(pos.eval+1)= *(pos.eval);
           pos.eval++;
           pos.eval->update(pos.osl_state,pv[ply]);
           insert_pv_in_tt_rec(pos,ply+1);
           --pos.eval;
           }
           );
    }
  }
#endif

  // insert_pv_in_tt() is called at the end of a search iteration, and inserts
  // the PV back into the TT. This makes sure the old PV moves are searched
  // first, even if the old TT entries have been overwritten.

  void RootMove::insert_pv_in_tt(Position& pos) {

#ifndef GPSFISH
    StateInfo state[PLY_MAX_PLUS_2], *st = state;
    TTEntry* tte;
    Key k;
    Value v, m = VALUE_NONE;
    int ply = 0;
#endif

    assert(pv[0] != MOVE_NONE && pos.is_pseudo_legal(pv[0]));

#ifdef GPSFISH
    insert_pv_in_tt_rec(pos,0);
#else
    do {
        k = pos.get_key();
        tte = TT.probe(k);

        // Don't overwrite existing correct entries
        if (!tte || tte->move() != pv[ply])
        {
            v = (pos.in_check() ? VALUE_NONE : evaluate(pos, m));
            TT.store(k, VALUE_NONE, VALUE_TYPE_NONE, DEPTH_NONE, pv[ply], v, m);
        }
        pos.do_move(pv[ply], *st++);

    } while (pv[++ply] != MOVE_NONE);

    do pos.undo_move(pv[--ply]); while (ply);
#endif
  }

} // namespace


/// Thread::idle_loop() is where the thread is parked when it has no work to do.
/// The parameter 'sp', if non-NULL, is a pointer to an active SplitPoint object
/// for which the thread is the master.

void Thread::idle_loop(SplitPoint* sp) {

  while (true)
  {
      // If we are not searching, wait for a condition to be signaled
      // instead of wasting CPU time polling for work.
      while (   do_sleep
             || do_terminate
             || (Threads.use_sleeping_threads() && !is_searching))
      {
          assert((!sp && threadID) || Threads.use_sleeping_threads());

          if (do_terminate)
          {
              assert(!sp);
              return;
          }

          // Grab the lock to avoid races with Thread::wake_up()
          lock_grab(&sleepLock);

          // If we are master and all slaves have finished don't go to sleep
          if (sp && Threads.split_point_finished(sp))
          {
              lock_release(&sleepLock);
              break;
          }

          // Do sleep after retesting sleep conditions under lock protection, in
          // particular we need to avoid a deadlock in case a master thread has,
          // in the meanwhile, allocated us and sent the wake_up() call before we
          // had the chance to grab the lock.
          if (do_sleep || !is_searching)
              cond_wait(&sleepCond, &sleepLock);

          lock_release(&sleepLock);
      }

      // If this thread has been assigned work, launch a search
      if (is_searching)
      {
          assert(!do_terminate);

          // Copy split point position and search stack and call search()
#ifdef MOVE_STACK_REJECTIONS
          SearchStack ss_base[PLY_MAX_PLUS_2];
          SplitPoint* tsp = threads[threadID].splitPoint;
          Position pos(*tsp->pos, threadID);
          int ply=tsp->ss->ply;
          assert(0< ply && ply+3<PLY_MAX_PLUS_2);
          for(int i=0;i<ply-1;i++)
              ss_base[i].currentMove=(tsp->ss-ply+i)->currentMove;
          SearchStack *ss= &ss_base[ply-1];
#else
          Stack ss[PLY_MAX_PLUS_2];
          SplitPoint* tsp = splitPoint;
          Position pos(*tsp->pos, threadID);
#endif

          memcpy(ss, tsp->ss - 1, 4 * sizeof(Stack));
          (ss+1)->sp = tsp;

#ifdef GPSFISH
          uint64_t es_base[(PLY_MAX_PLUS_2*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)];
          eval_t *es=(eval_t *)&es_base[0];
          assert(tsp->pos->eval);
          es[0]= *(tsp->pos->eval);
          pos.eval= &es[0];
#endif

          if (tsp->nodeType == Root)
              search<SplitPointRoot>(pos, ss+1, tsp->alpha, tsp->beta, tsp->depth);
          else if (tsp->nodeType == PV)
              search<SplitPointPV>(pos, ss+1, tsp->alpha, tsp->beta, tsp->depth);
          else if (tsp->nodeType == NonPV)
              search<SplitPointNonPV>(pos, ss+1, tsp->alpha, tsp->beta, tsp->depth);
          else
              assert(false);

          assert(is_searching);

          is_searching = false;

          // Wake up master thread so to allow it to return from the idle loop in
          // case we are the last slave of the split point.
          if (   Threads.use_sleeping_threads()
              && threadID != tsp->master
              && !Threads[tsp->master].is_searching)
              Threads[tsp->master].wake_up();
      }

      // If this thread is the master of a split point and all slaves have
      // finished their work at this split point, return from the idle loop.
      if (sp && Threads.split_point_finished(sp))
      {
          // Because sp->is_slave[] is reset under lock protection,
          // be sure sp->lock has been released before to return.
          lock_grab(&(sp->lock));
          lock_release(&(sp->lock));
          return;
      }
  }
}

#ifdef GPSFISHONE
void do_checkmate(Position& pos, int mateTime){
    cout << "checkmate notimplemented";
    return;
}
#else
void do_checkmate(Position& pos, int mateTime){
    Signals.stop=false;
    osl::state::NumEffectState state(pos.osl_state);
#if (! defined ALLOW_KING_ABSENCE)
    if (state.kingSquare(state.turn()).isPieceStand()) {
        cout << "checkmate notimplemented";
        return;
    }
#endif
    osl::checkmate::DfpnTable table(state.turn());
    const osl::PathEncoding path(state.turn());
    osl::Move checkmate_move;
    osl::stl::vector<osl::Move> pv;
    osl::checkmate::ProofDisproof result;
    osl::checkmate::Dfpn dfpn;
    dfpn.setTable(&table);
    double seconds=(double)mateTime/1000.0;
    osl::misc::MilliSeconds start = osl::misc::MilliSeconds::now();
    size_t step = 100000, total = 0;
    double scale = 1.0; 
    for (size_t limit = step; true; limit = static_cast<size_t>(step*scale)) {
        result = dfpn.
            hasCheckmateMove(state, osl::hash::HashKey(state), path, limit, checkmate_move, Move(), &pv);
        double elapsed = start.elapsedSeconds();
        double memory = osl::OslConfig::memoryUseRatio();
        uint64_t node_count = dfpn.nodeCount();
        cout << "info time " << static_cast<int>(elapsed*1000)
            << " nodes " << total+node_count << " nps " << static_cast<int>(node_count/elapsed)
            << " hashfull " << static_cast<int>(memory*1000) << "\n";
        //poll(pos);
        if (result.isFinal() || elapsed >= seconds || memory > 0.9 || Signals.stop)
            break;
        total += limit;
        // estimate: total * std::min(seconds/elapsed, 1.0/memory)
        // next: (estimate - total) / 2 + total
        scale = (total * std::min(seconds/elapsed, 1.0/memory) - total) / 2.0 / step;
        scale = std::max(std::min(16.0, scale), 0.1);
    }
    if (! result.isFinal()) {
        cout << "checkmate timeout\n";
        return;
    }
    if (! result.isCheckmateSuccess()) {
        cout << "checkmate nomate\n";
        return;
    }
    std::string msg = "checkmate";
    for (size_t i=0; i<pv.size(); ++i)
        msg += " " + move_to_uci(pv[i],false);
    cout << msg << "\n" << std::flush;
}
#endif

void show_tree(Position &pos){
    show_tree_rec(pos);
}

/// do_timer_event() is called by the timer thread when the timer triggers. It
/// is used to print debug info and, more important, to detect when we are out of
/// available time and so stop the search.

void do_timer_event() {

  static int lastInfoTime;
  int e = elapsed_time();

  if (get_system_time() - lastInfoTime >= 1000 || !lastInfoTime)
  {
      lastInfoTime = get_system_time();

      dbg_print_mean();
      dbg_print_hit_rate();
  }

  if (Limits.ponder)
      return;

  bool stillAtFirstMove =    Signals.firstRootMove
                         && !Signals.failedLowAtRoot
                         &&  e > TimeMgr.available_time();

  bool noMoreTime =   e > TimeMgr.maximum_time()
                   || stillAtFirstMove;

  if (   (Limits.useTimeManagement() && noMoreTime)
      || (Limits.maxTime && e >= Limits.maxTime)
         /* missing nodes limit */ ) // FIXME
      Signals.stop = true;
}
