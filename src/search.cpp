/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2012 Marco Costalba, Joona Kiiski, Tord Romstad

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
#include <iostream>
#include <sstream>

#include "book.h"
#include "evaluate.h"
#include "history.h"
#include "movegen.h"
#include "movepick.h"
#include "notation.h"
#include "search.h"
#include "timeman.h"
#include "thread.h"
#include "tt.h"
#include "ucioption.h"

#ifdef GPSFISH
#include "bitops.h"
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
  std::vector<RootMove> RootMoves;
  Position RootPos;
  Color RootColor;
  Time::point SearchTime;
  StateStackPtr SetupStates;
}

using std::string;
using Eval::evaluate;
using namespace Search;

namespace {

  // Set to true to force running with one thread. Used for debugging
  const bool FakeSplit = false;

  // This is the minimum interval in msec between two check_time() calls
  const int TimerResolution = 5;

  // Different node types, used as template parameter
  enum NodeType { Root, PV, NonPV, SplitPointRoot, SplitPointPV, SplitPointNonPV };

  // Dynamic razoring margin based on depth
  inline Value razor_margin(Depth d) { return Value(512 + 16 * int(d)); }

  // Futility lookup tables (initialized at startup) and their access functions
  Value FutilityMargins[16][64]; // [depth][moveNumber]
  int FutilityMoveCounts[32];    // [depth]

  inline Value futility_margin(Depth d, int mn) {

    return d < 7 * ONE_PLY ? FutilityMargins[std::max(int(d), 1)][std::min(mn, 63)]
                           : 2 * VALUE_INFINITE;
  }

  // Reduction lookup tables (initialized at startup) and their access function
  int8_t Reductions[2][64][64]; // [pv][depth][moveNumber]

  template <bool PvNode> inline Depth reduction(Depth d, int mn) {

    return (Depth) Reductions[PvNode][std::min(int(d) / ONE_PLY, 63)][std::min(mn, 63)];
  }

  size_t PVSize, PVIdx;
  TimeManager TimeMgr;
  int BestMoveChanges;
  Value DrawValue[COLOR_NB];
  History H;

  template <NodeType NT>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth);

  template <NodeType NT, bool InCheck>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth);

  void id_loop(Position& pos);
  Value value_to_tt(Value v, int ply);
  Value value_from_tt(Value v, int ply);
  bool check_is_dangerous(Position& pos, Move move, Value futilityBase, Value beta);
  bool yields_to_threat(const Position& pos, Move move, Move threat);
  bool prevents_threat(const Position& pos, Move move, Move threat);
  string uci_pv(const Position& pos, int depth, Value alpha, Value beta);

  struct Skill {
    Skill(int l) : level(l), best(MOVE_NONE) {}
   ~Skill() {
      if (enabled()) // Swap best PV line with the sub-optimal one
          std::swap(RootMoves[0], *std::find(RootMoves.begin(),
                    RootMoves.end(), best ? best : pick_move()));
    }

    bool enabled() const { return level < 20; }
    bool time_to_pick(int depth) const { return depth == 1 + level; }
    Move pick_move();

    int level;
    Move best;
  };

#ifdef GPSFISH
  void show_tree_rec(Position &pos){
    TTEntry* tte;
    StateInfo st;
    if ((tte = TT.probe(pos.key())) != NULL){
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

  inline Value value_draw(Position const& pos) {
    return DrawValue[pos.side_to_move()];
  }

  bool can_capture_king(Position const& pos){
    Color us=pos.side_to_move();
    Color them=~us;
    const osl::Square king = pos.king_square(them);
    return pos.osl_state.hasEffectAt(us, king);
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
} // namespace


/// Search::init() is called during startup to initialize various lookup tables

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
      FutilityMoveCounts[d] = int(3.001 + 0.25 * pow(double(d), 2.0));
}


/// Search::perft() is our utility to verify move generation. All the leaf nodes
/// up to the given depth are generated and counted and the sum returned.

size_t Search::perft(Position& pos, Depth depth) {

  // At the last ply just return the number of legal moves (leaf nodes)
  if (depth == ONE_PLY)
      return MoveList<LEGAL>(pos).size();

  StateInfo st;
  size_t cnt = 0;
  CheckInfo ci(pos);

  for (MoveList<LEGAL> ml(pos); !ml.end(); ++ml)
  {
#ifdef GPSFISH
      pos.do_undo_move(ml.move(),st,
              [&](osl::Square){
              assert(pos.is_ok());
#else
      pos.do_move(ml.move(), st, ci, pos.move_gives_check(ml.move(), ci));
#endif
      cnt += perft(pos, depth - ONE_PLY);
#ifdef GPSFISH
      } );
#else
      pos.undo_move(ml.move());
#endif
  }

  return cnt;
}

/// Search::think() is the external interface to Stockfish's search, and is
/// called by the main thread when the program receives the UCI 'go' command. It
/// searches from RootPos and at the end prints the "bestmove" to output.

void Search::think() {

  static PolyglotBook book; // Defined static to initialize the PRNG only once

  RootColor = RootPos.side_to_move();
  TimeMgr.init(Limits, RootPos.startpos_ply_counter(), RootColor);

#ifdef GPSFISH
  const Value VALUE_DRAW = value_draw(RootPos);
#endif


  if (RootMoves.empty())
  {
      RootMoves.push_back(MOVE_NONE);
      sync_cout << "info depth 0 score "
                << score_to_uci(RootPos.in_check() ? -VALUE_MATE : VALUE_DRAW)
                << sync_endl;

      goto finalize;
  }

  if (Options["OwnBook"] && !Limits.infinite)
  {
      Move bookMove = book.probe(RootPos, Options["Book File"], Options["Best Book Move"]);

      if (bookMove && std::count(RootMoves.begin(), RootMoves.end(), bookMove))
      {
          std::swap(RootMoves[0], *std::find(RootMoves.begin(), RootMoves.end(), bookMove));
          goto finalize;
      }
  }

#ifdef GPSFISH
  DrawValue[BLACK] =  VALUE_DRAW;
  DrawValue[WHITE] = -VALUE_DRAW;
#else
  if (Options["Contempt Factor"] && !Options["UCI_AnalyseMode"])
  {
      int cf = Options["Contempt Factor"] * PawnValueMg / 100; // From centipawns
      cf = cf * MaterialTable::game_phase(RootPos) / PHASE_MIDGAME; // Scale down with phase
      DrawValue[ RootColor] = VALUE_DRAW - Value(cf);
      DrawValue[~RootColor] = VALUE_DRAW + Value(cf);
  }
  else
      DrawValue[WHITE] = DrawValue[BLACK] = VALUE_DRAW;
#endif

  if (Options["Use Search Log"])
  {
      Log log(Options["Search Log Filename"]);
      log << "\nSearching: "  << RootPos.fen()
          << "\ninfinite: "   << Limits.infinite
          << " ponder: "      << Limits.ponder
          << " time: "        << Limits.time[RootColor]
          << " increment: "   << Limits.inc[RootColor]
          << " moves to go: " << Limits.movestogo
          << std::endl;
  }

  Threads.wake_up();

  // Set best timer interval to avoid lagging under time pressure. Timer is
  // used to check for remaining available thinking time.
  if (Limits.use_time_management())
      Threads.set_timer(std::min(100, std::max(TimeMgr.available_time() / 16,
                                               TimerResolution)));
  else if (Limits.nodes)
      Threads.set_timer(2 * TimerResolution);
  else
      Threads.set_timer(100);

  id_loop(RootPos); // Let's start searching !

  Threads.set_timer(0); // Stop timer
  Threads.sleep();

  if (Options["Use Search Log"])
  {
      Time::point elapsed = Time::now() - SearchTime + 1;

      Log log(Options["Search Log Filename"]);
      log << "Nodes: "          << RootPos.nodes_searched()
          << "\nNodes/second: " << RootPos.nodes_searched() * 1000 / elapsed
          << "\nBest move: "    << move_to_san(RootPos, RootMoves[0].pv[0]);

      StateInfo st;
#ifdef GPSFISH
      if(RootMoves[0].pv[0].isNormal())
          RootPos.do_undo_move(RootMoves[0].pv[0],st,
                  [&](osl::Square){
                  assert(pos.is_ok());
#else
      RootPos.do_move(RootMoves[0].pv[0], st);
#endif
      log << "\nPonder move: " << move_to_san(RootPos, RootMoves[0].pv[1]) << std::endl;
#ifdef GPSFISH
      } );
#else
      RootPos.undo_move(RootMoves[0].pv[0]);
#endif
  }

finalize:

  // When we reach max depth we arrive here even without Signals.stop is raised,
  // but if we are pondering or in infinite search, we shouldn't print the best
  // move before we are told to do so.
  if (!Signals.stop && (Limits.ponder || Limits.infinite))
      RootPos.this_thread()->wait_for_stop_or_ponderhit();

  // Best move could be MOVE_NONE when searching on a stalemate position
  sync_cout << "bestmove " << move_to_uci(RootMoves[0].pv[0], RootPos.is_chess960())
#ifdef GPSFISH
            << (RootMoves[0].pv[1].isNormal() ? " ponder " + move_to_uci(RootMoves[0].pv[1], RootPos.is_chess960()) : "" )
#else
            << " ponder "  << move_to_uci(RootMoves[0].pv[1], RootPos.is_chess960())
#endif
            << sync_endl;
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
        TTEntry* tte = TT.probe(pos.key());
        if (tte && tte->type() == BOUND_EXACT
                && tte->depth() >= CheckmateDepth) {
            Value v = value_from_tt(tte->value(), 0);
            if (v >= VALUE_MATE_IN_MAX_PLY || v < VALUE_MATED_IN_MAX_PLY)
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
            TT.store(pos.key(), mate_in(pv.size()),
                    BOUND_EXACT, CheckmateDepth, checkmate_move,
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
                sync_cout << "info string checkmate in future (" << first
                    << ") " << move_to_uci(moves[first],false)
                    << " by " << move_to_uci(*result,false) << sync_endl;
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
            //RootMoves[i].non_pv_score = VALUE_MATED_IN_MAX_PLY;
            sync_cout << "info string losing move " << i << "th "
                << move_to_uci(RootMoves[i].pv[0],false)
                << " by " << move_to_uci(win_move,false) << sync_endl;
        }
    }
    solver->clear();
}
#endif

namespace {

  // id_loop() is the main iterative deepening loop. It calls search() repeatedly
  // with increasing depth until the allocated thinking time has been consumed,
  // user stops the search, or the maximum search depth is reached.

  void id_loop(Position& pos) {

    Stack ss[MAX_PLY_PLUS_2];
#ifdef GPSFISH
    uint64_t es_base[(MAX_PLY_PLUS_2*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)]
#ifdef __GNUC__
      __attribute__((aligned(16)))
#endif
	;
    eval_t *es=(eval_t *)&es_base[0];
#endif

    int depth, prevBestMoveChanges;
    Value bestValue, alpha, beta, delta;
    bool bestMoveNeverChanged = true;

    memset(ss, 0, 4 * sizeof(Stack));
    depth = BestMoveChanges = 0;
    bestValue = delta = -VALUE_INFINITE;
#ifdef GPSFISH
    ss->currentMove = osl::Move::PASS(pos.side_to_move()); // Hack to skip update_gains
#else
    ss->currentMove = MOVE_NULL; // Hack to skip update gains
#endif
    TT.new_search();
    H.clear();

    PVSize = Options["MultiPV"];
    Skill skill(Options["Skill Level"]);

    // Do we have to play with skill handicap? In this case enable MultiPV search
    // that we will use behind the scenes to retrieve a set of possible moves.
    if (skill.enabled() && PVSize < 4)
        PVSize = 4;

    PVSize = std::min(PVSize, RootMoves.size());

#ifdef GPSFISH
    pos.eval= &es[0];
    *(pos.eval)=eval_t(pos.osl_state,false);
#endif

#ifdef GPSFISH_DFPN
    uint64_t next_checkmate = 1<<18;
#endif

    // Iterative deepening loop until requested to stop or target depth reached
    while (++depth <= MAX_PLY && !Signals.stop && (!Limits.depth || depth <= Limits.depth))
    {
        // Save last iteration's scores before first PV line is searched and all
        // the move scores but the (new) PV are set to -VALUE_INFINITE.
        for (size_t i = 0; i < RootMoves.size(); i++)
            RootMoves[i].prevScore = RootMoves[i].score;

        prevBestMoveChanges = BestMoveChanges; // Only sensible when PVSize == 1
        BestMoveChanges = 0;

#ifdef GPSFISH_DFPN
        if ((uint64_t)pos.nodes_searched() > next_checkmate
                && ((Time::now() - SearchTime + 1000)
                   < std::max(Limits.movetime,TimeMgr.maximum_time())*4/5) ) {
            run_checkmate(depth, next_checkmate, pos);
            next_checkmate *= 2;
            if (RootMoves[0].score <= VALUE_MATED_IN_MAX_PLY) {
                depth -= std::min(4, (int)depth/2);
                alpha = std::max(alpha - delta*63, -VALUE_INFINITE);
                beta  = std::min(beta  + delta*63,  VALUE_INFINITE);
            }
        }
#endif

        // MultiPV loop. We perform a full root search for each PV line
        for (PVIdx = 0; PVIdx < PVSize; PVIdx++)
        {
            // Set aspiration window default width
            if (depth >= 5 && abs(RootMoves[PVIdx].prevScore) < VALUE_KNOWN_WIN)
            {
                delta = Value(16);
                alpha = RootMoves[PVIdx].prevScore - delta;
                beta  = RootMoves[PVIdx].prevScore + delta;
            }
            else
            {
                alpha = -VALUE_INFINITE;
                beta  =  VALUE_INFINITE;
            }

            // Start with a small aspiration window and, in case of fail high/low,
            // research with bigger window until not failing high/low anymore.
            while (true)
            {
                // Search starts from ss+1 to allow referencing (ss-1). This is
                // needed by update gains and ss copy when splitting at Root.
                bestValue = search<Root>(pos, ss+1, alpha, beta, depth * ONE_PLY);

                // Bring to front the best move. It is critical that sorting is
                // done with a stable algorithm because all the values but the first
                // and eventually the new best one are set to -VALUE_INFINITE and
                // we want to keep the same order for all the moves but the new
                // PV that goes to the front. Note that in case of MultiPV search
                // the already searched PV lines are preserved.
                sort<RootMove>(RootMoves.begin() + PVIdx, RootMoves.end());

                // Write PV back to transposition table in case the relevant
                // entries have been overwritten during the search.
                for (size_t i = 0; i <= PVIdx; i++)
                    RootMoves[i].insert_pv_in_tt(pos);

                // If search has been stopped return immediately. Sorting and
                // writing PV back to TT is safe becuase RootMoves is still
                // valid, although refers to previous iteration.
                if (Signals.stop)
                    return;

                // In case of failing high/low increase aspiration window and
                // research, otherwise exit the loop.
                if (bestValue > alpha && bestValue < beta)
                    break;

                // Give some update (without cluttering the UI) before to research
                if (Time::now() - SearchTime > 3000)
                    sync_cout << uci_pv(pos, depth, alpha, beta) << sync_endl;

                if (abs(bestValue) >= VALUE_KNOWN_WIN)
                {
                    alpha = -VALUE_INFINITE;
                    beta  =  VALUE_INFINITE;
                }
                else if (bestValue >= beta)
                {
                    beta += delta;
                    delta += delta / 2;
                }
                else
                {
                    Signals.failedLowAtRoot = true;
                    Signals.stopOnPonderhit = false;

                    alpha -= delta;
                    delta += delta / 2;
                }

                assert(alpha >= -VALUE_INFINITE && beta <= VALUE_INFINITE);
            }

            // Sort the PV lines searched so far and update the GUI
            sort<RootMove>(RootMoves.begin(), RootMoves.begin() + PVIdx + 1);
            sync_cout << uci_pv(pos, depth, alpha, beta) << sync_endl;
        }

        // Do we need to pick now the sub-optimal best move ?
        if (skill.enabled() && skill.time_to_pick(depth))
            skill.pick_move();

        if (Options["Use Search Log"])
        {
            Log log(Options["Search Log Filename"]);
            log << pretty_pv(pos, depth, bestValue, Time::now() - SearchTime, &RootMoves[0].pv[0])
                << std::endl;
        }

        // Filter out startup noise when monitoring best move stability
        if (depth > 2 && BestMoveChanges)
            bestMoveNeverChanged = false;

        // Do we have time for the next iteration? Can we stop searching now?
        if (Limits.use_time_management() && !Signals.stopOnPonderhit)
        {
            bool stop = false; // Local variable, not the volatile Signals.stop

            // Take in account some extra time if the best move has changed
            if (depth > 4 && depth < 50 &&  PVSize == 1)
                TimeMgr.pv_instability(BestMoveChanges, prevBestMoveChanges);

            // Stop search if most of available time is already consumed. We
            // probably don't have enough time to search the first move at the
            // next iteration anyway.
            if (Time::now() - SearchTime > (TimeMgr.available_time() * 62) / 100)
                stop = true;

            // Stop search early if one move seems to be much better than others
            if (    depth >= 12
                && !stop
                &&  PVSize == 1
                && (   (bestMoveNeverChanged &&  pos.captured_piece_type())
                    || Time::now() - SearchTime > (TimeMgr.available_time() * 40) / 100))
            {
                Value rBeta = bestValue - 2 * PawnValueMg;
                (ss+1)->excludedMove = RootMoves[0].pv[0];
                (ss+1)->skipNullMove = true;
                Value v = search<NonPV>(pos, ss+1, rBeta - 1, rBeta, (depth - 3) * ONE_PLY);
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

    assert(alpha >= -VALUE_INFINITE && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(depth > DEPTH_ZERO);

    Move movesSearched[64];
    StateInfo st;
    const TTEntry *tte;
    SplitPoint* sp;
    Key posKey;
    Move ttMove, move, excludedMove, bestMove, threatMove;
    Depth ext, newDepth;
    Value bestValue, value, ttValue;
    Value eval, nullValue, futilityValue;
    bool inCheck, givesCheck, pvMove, singularExtensionNode;
    bool captureOrPromotion, dangerous, doFullDepthSearch;
    int moveCount, playedMoveCount;

    // Step 1. Initialize node
    Thread* thisThread = pos.this_thread();
    moveCount = playedMoveCount = 0;

#ifdef GPSFISH
    int repeat_check = 0;
    const Value VALUE_DRAW = value_draw(pos);

    if(can_capture_king(pos)){
        return mate_in(0);
    }
#endif

    inCheck = pos.in_check();

    if (SpNode)
    {
        sp = ss->sp;
        bestMove   = sp->bestMove;
        threatMove = sp->threatMove;
        bestValue  = sp->bestValue;
        tte = NULL;
        ttMove = excludedMove = MOVE_NONE;
        ttValue = VALUE_NONE;

        assert(sp->bestValue > -VALUE_INFINITE && sp->moveCount > 0);

        goto split_point_start;
    }

    bestValue = -VALUE_INFINITE;
    ss->currentMove = threatMove = (ss+1)->excludedMove = bestMove = MOVE_NONE;
    ss->ply = (ss-1)->ply + 1;
    (ss+1)->skipNullMove = false; (ss+1)->reduction = DEPTH_ZERO;
    (ss+2)->killers[0] = (ss+2)->killers[1] = MOVE_NONE;

    // Used to send selDepth info to GUI
    if (PvNode && thisThread->maxPly < ss->ply)
        thisThread->maxPly = ss->ply;

#ifdef GPSFISH
    // Step X. Check for aborted search and immediate draw
    // Check for an instant draw or maximum ply reached
    if (Signals.stop || ss->ply > MAX_PLY || pos.is_draw(repeat_check))
        return VALUE_DRAW;

    if(repeat_check<0)
        return mated_in(ss->ply+1);
    else if(repeat_check>0)
        return mate_in(ss->ply);

    // Step 2. Check for aborted search and immediate draw
    if ((   Signals.stop
         || pos.is_draw<true,PvNode>()
         || ss->ply > MAX_PLY) && !RootNode)
        return VALUE_DRAW;

    if ( !Root ){
        if(repeat_check<0)
            return mated_in(ss->ply);
        else if(repeat_check>0)
            return mate_in(ss->ply);
        else if(osl::EnterKing::canDeclareWin(pos.osl_state))
            return mate_in(ss->ply+1);
    }

    if (!ss->checkmateTested) {
        ss->checkmateTested = true;
        if(!pos.osl_state.inCheck()
                && ImmediateCheckmate::hasCheckmateMove
                (pos.side_to_move(),pos.osl_state,bestMove)) {
            return mate_in(ss->ply);
        }
#  ifdef GPSFISH_CHECKMATE3
        if ((! (ss-1)->currentMove.isNormal()
            || (ss-1)->currentMove.ptype() == osl::KING)) {
            osl::checkmate::King8Info king8=pos.osl_state.king8Info(alt(pos.side_to_move()));
            assert(king8.uint64Value() == osl::checkmate::King8Info::make(pos.side_to_move(), pos.osl_state).uint64Value());
            bool in_danger = king8.dropCandidate() | king8.moveCandidate2();
            if (in_danger) {
                osl::checkmate::FixedDepthSearcher solver(pos.osl_state);
                if (solver.hasCheckmateMoveOfTurn(2,bestMove)
                        .isCheckmateSuccess()) {
                    return mate_in(ss->ply+2);;
                }
            }
        }
#  endif
    }
#endif

    if (!RootNode)
    {
        // Step 2. Check for aborted search and immediate draw
        if (Signals.stop || pos.is_draw<true, PvNode>() || ss->ply > MAX_PLY)
            return DrawValue[pos.side_to_move()];

        // Step 3. Mate distance pruning. Even if we mate at the next move our score
        // would be at best mate_in(ss->ply+1), but if alpha is already bigger because
        // a shorter mate was found upward in the tree then there is no need to search
        // further, we will never beat current alpha. Same logic but with reversed signs
        // applies also in the opposite condition of being mated instead of giving mate,
        // in this case return a fail-high score.
        alpha = std::max(mated_in(ss->ply), alpha);
        beta = std::min(mate_in(ss->ply+1), beta);
        if (alpha >= beta)
            return alpha;
    }

    // Step 4. Transposition table lookup
    // We don't want the score of a partial search to overwrite a previous full search
    // TT value, so we use a different position key in case of an excluded move.
    excludedMove = ss->excludedMove;
#ifdef GPSFISH
    posKey = excludedMove!=MOVE_NONE ? pos.exclusion_key() : pos.key();
#else
    posKey = excludedMove ? pos.exclusion_key() : pos.key();
#endif

    tte = TT.probe(posKey);
#ifdef GPSFISH
    ttMove = RootNode ? RootMoves[PVIdx].pv[0] : tte ? tte->move(pos) : MOVE_NONE;
#else
    ttMove = RootNode ? RootMoves[PVIdx].pv[0] : tte ? tte->move() : MOVE_NONE;
#endif
    ttValue = tte ? value_from_tt(tte->value(), ss->ply) : VALUE_NONE;

    // At PV nodes we check for exact scores, while at non-PV nodes we check for
    // a fail high/low. Biggest advantage at probing at PV nodes is to have a
    // smooth experience in analysis mode. We don't probe at Root nodes otherwise
    // we should also update RootMoveList to avoid bogus output.
    if (   !RootNode
        && tte
        && tte->depth() >= depth
        && ttValue != VALUE_NONE // Only in case of TT access race
        && (           PvNode ?  tte->type() == BOUND_EXACT
            : ttValue >= beta ? (tte->type() & BOUND_LOWER)
                              : (tte->type() & BOUND_UPPER)))
    {
        TT.refresh(tte);
        ss->currentMove = ttMove; // Can be MOVE_NONE

        if (    ttValue >= beta
            &&  ttMove
            && !pos.is_capture_or_promotion(ttMove)
            &&  ttMove != ss->killers[0])
        {
            ss->killers[1] = ss->killers[0];
            ss->killers[0] = ttMove;
        }
        return ttValue;
    }

    // Step 5. Evaluate the position statically and update parent's gain statistics
    if (inCheck)
        ss->staticEval = ss->evalMargin = eval = VALUE_NONE;

    else if (tte)
    {
        // Following asserts are valid only in single thread condition because
        // TT access is always racy and its contents cannot be trusted.
        assert(tte->static_value() != VALUE_NONE || Threads.size() > 1);
        assert(ttValue != VALUE_NONE || tte->type() == BOUND_NONE || Threads.size() > 1);

        ss->staticEval = eval = tte->static_value();
        ss->evalMargin = tte->static_value_margin();

        if (eval == VALUE_NONE || ss->evalMargin == VALUE_NONE) // Due to a race
            eval = ss->staticEval = evaluate(pos, ss->evalMargin);

        // Can ttValue be used as a better position evaluation?
        if (ttValue != VALUE_NONE)
            if (   ((tte->type() & BOUND_LOWER) && ttValue > eval)
                || ((tte->type() & BOUND_UPPER) && ttValue < eval))
                eval = ttValue;
    }
    else
    {
        eval = ss->staticEval = evaluate(pos, ss->evalMargin);
        TT.store(posKey, VALUE_NONE, BOUND_NONE, DEPTH_NONE, MOVE_NONE,
                 ss->staticEval, ss->evalMargin);
    }

    // Update gain for the parent non-capture move given the static position
    // evaluation before and after the move.
#ifdef GPSFISH
    if (  !(move = (ss-1)->currentMove).isPass()
#else
    if (   (move = (ss-1)->currentMove) != MOVE_NULL
#endif
        && (ss-1)->staticEval != VALUE_NONE
        &&  ss->staticEval != VALUE_NONE
        && !pos.captured_piece_type()
        &&  type_of(move) == NORMAL)
    {
        Square to = to_sq(move);
#ifdef GPSFISH
        //H.update_gain(m.ptypeO(), to_sq(m), -(before + after));
        H.update_gain(move.ptypeO(), to, -(ss-1)->staticEval - ss->staticEval);
#else
        H.update_gain(pos.piece_on(to), to, -(ss-1)->staticEval - ss->staticEval);
#endif
    }

    // Step 6. Razoring (is omitted in PV nodes)
    if (   !PvNode
        &&  depth < 4 * ONE_PLY
        && !inCheck
        &&  eval + razor_margin(depth) < beta
        &&  ttMove == MOVE_NONE
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY
#ifndef GPSFISH
        && !pos.pawn_on_7th(pos.side_to_move()))
#endif
      )
    {
        Value rbeta = beta - razor_margin(depth);
        Value v = qsearch<NonPV, false>(pos, ss, rbeta-1, rbeta, DEPTH_ZERO);
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
        &&  depth < 4 * ONE_PLY
        && !inCheck
        &&  eval - FutilityMargins[depth][0] >= beta
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY
#ifndef GPSFISH
        &&  pos.non_pawn_material(pos.side_to_move())
#endif
	   )
        return eval - FutilityMargins[depth][0];

    // Step 8. Null move search with verification search (is omitted in PV nodes)
    if (   !PvNode
        && !ss->skipNullMove
        &&  depth > ONE_PLY
        && !inCheck
        &&  eval >= beta
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY
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
        Depth R = 3 * ONE_PLY + depth / 4;

        // Null move dynamic reduction based on value
        if (eval - PawnValueMg > beta)
            R += ONE_PLY;

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
        nullValue = depth-R < ONE_PLY ? -qsearch<NonPV, false>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                      : - search<NonPV>(pos, ss+1, -beta, -alpha, depth-R);
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
            if (nullValue >= VALUE_MATE_IN_MAX_PLY)
                nullValue = beta;

            if (depth < 6 * ONE_PLY)
                return nullValue;

            // Do verification search at high depths
            ss->skipNullMove = true;
            Value v = search<NonPV>(pos, ss, alpha, beta, depth-R);
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
            threatMove = (ss+1)->currentMove;

            if (   depth < 5 * ONE_PLY
                && (ss-1)->reduction
                && threatMove != MOVE_NONE
                && yields_to_threat(pos, (ss-1)->currentMove, threatMove))
                return beta - 1;
        }
    }

    // Step 9. ProbCut (is omitted in PV nodes)
    // If we have a very good capture (i.e. SEE > seeValues[captured_piece_type])
    // and a reduced search returns a value much above beta, we can (almost) safely
    // prune the previous move.
    if (   !PvNode
        &&  depth >= 5 * ONE_PLY
        && !inCheck
        && !ss->skipNullMove
        &&  excludedMove == MOVE_NONE
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY)
    {
        Value rbeta = beta + 200;
        Depth rdepth = depth - ONE_PLY - 3 * ONE_PLY;

        assert(rdepth >= ONE_PLY);
        assert((ss-1)->currentMove != MOVE_NONE);
        assert((ss-1)->currentMove != MOVE_NULL);

        MovePicker mp(pos, ttMove, H, pos.captured_piece_type());
        CheckInfo ci(pos);

        while ((move = mp.next_move<false>()) != MOVE_NONE)
            if (pos.pl_move_is_legal(move, ci.pinned))
            {
                ss->currentMove = move;
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
                pos.undo_move(move);
#endif
                if (value >= rbeta)
                    return value;
            }
    }

    // Step 10. Internal iterative deepening
    if (   depth >= (PvNode ? 5 * ONE_PLY : 8 * ONE_PLY)
        && ttMove == MOVE_NONE
        && (PvNode || (!inCheck && ss->staticEval + Value(256) >= beta)))
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

    MovePicker mp(pos, ttMove, depth, H, ss, PvNode ? -VALUE_INFINITE : beta);
    CheckInfo ci(pos);
    value = bestValue; // Workaround a bogus 'uninitialized' warning under gcc
    singularExtensionNode =   !RootNode
                           && !SpNode
                           &&  depth >= (PvNode ? 6 * ONE_PLY : 8 * ONE_PLY)
                           &&  ttMove != MOVE_NONE
#ifdef GPSFISH
                           && excludedMove==MOVE_NONE // Recursive singular search is not allowed
#else
                           && !excludedMove // Recursive singular search is not allowed
#endif
                           && (tte->type() & BOUND_LOWER)
                           &&  tte->depth() >= depth - 3 * ONE_PLY;

    // Step 11. Loop through moves
    // Loop through all pseudo-legal moves until no moves remain or a beta cutoff occurs
    while ((move = mp.next_move<SpNode>()) != MOVE_NONE)
    {
      assert(is_ok(move));

      if (move == excludedMove)
          continue;

      // At root obey the "searchmoves" option and skip moves not listed in Root
      // Move List, as a consequence any illegal move is also skipped. In MultiPV
      // mode we also skip PV moves which have been already searched.
      if (RootNode && !std::count(RootMoves.begin() + PVIdx, RootMoves.end(), move))
          continue;

      if (SpNode)
      {
          // Shared counter cannot be decremented later if move turns out to be illegal
          if (!pos.pl_move_is_legal(move, ci.pinned))
              continue;

          moveCount = ++sp->moveCount;
          sp->mutex.unlock();
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
          Signals.firstRootMove = (moveCount == 1);

#if 1 //ndef GPSFISH
          if (thisThread == Threads.main_thread() && Time::now() - SearchTime > 2000)
              sync_cout << "info depth " << depth / ONE_PLY
                        << " currmove " << move_to_uci(move, pos.is_chess960())
                        << " currmovenumber " << moveCount + PVIdx << sync_endl;
#endif
      }

      ext = DEPTH_ZERO;
      captureOrPromotion = pos.is_capture_or_promotion(move);
      givesCheck = pos.move_gives_check(move, ci);
#ifdef GPSFISH
      dangerous =   givesCheck; // XXX : add other condition ?
#else
      dangerous =   givesCheck
                 || pos.is_passed_pawn_push(move)
                 || type_of(move) == CASTLE
                 || (   captureOrPromotion // Entering a pawn endgame?
                     && type_of(pos.piece_on(to_sq(move))) != PAWN
                     && type_of(move) == NORMAL
                     && (  pos.non_pawn_material(WHITE) + pos.non_pawn_material(BLACK)
                         - PieceValue[MG][pos.piece_on(to_sq(move))] == VALUE_ZERO));
#endif

      // Step 12. Extend checks and, in PV nodes, also dangerous moves
      if (PvNode && dangerous)
          ext = ONE_PLY;

      else if (givesCheck && pos.see_sign(move) >= 0)
          ext = ONE_PLY / 2;

      // Singular extension search. If all moves but one fail low on a search of
      // (alpha-s, beta-s), and just one fails high on (alpha, beta), then that move
      // is singular and should be extended. To verify this we do a reduced search
      // on all the other moves but the ttMove, if result is lower than ttValue minus
      // a margin then we extend ttMove.
      if (    singularExtensionNode
          &&  move == ttMove
          && !ext
          &&  pos.pl_move_is_legal(move, ci.pinned)
          &&  abs(ttValue) < VALUE_KNOWN_WIN)
      {
          assert(ttValue != VALUE_NONE);

          Value rBeta = ttValue - int(depth);
          ss->excludedMove = move;
          ss->skipNullMove = true;
          value = search<NonPV>(pos, ss, rBeta - 1, rBeta, depth / 2);
          ss->skipNullMove = false;
          ss->excludedMove = MOVE_NONE;

          if (value < rBeta)
              ext = rBeta >= beta ? ONE_PLY + ONE_PLY / 2 : ONE_PLY;
      }

      // Update current move (this must be done after singular extension search)
      newDepth = depth - ONE_PLY + ext;

      // Step 13. Futility pruning (is omitted in PV nodes)
      if (   !PvNode
          && !captureOrPromotion
          && !inCheck
          && !dangerous
          &&  move != ttMove
          && (bestValue > VALUE_MATED_IN_MAX_PLY || (   bestValue == -VALUE_INFINITE
                                                     && alpha > VALUE_MATED_IN_MAX_PLY)))
      {
          // Move count based pruning
          if (   depth < 16 * ONE_PLY
              && moveCount >= FutilityMoveCounts[depth]
#ifdef GPSFISH
              && (threatMove==MOVE_NONE || !prevents_threat(pos, move, threatMove)))
#else
              && (!threatMove || !prevents_threat(pos, move, threatMove)))
#endif
          {
              if (SpNode)
                  sp->mutex.lock();

              continue;
          }

          // Value based pruning
          // We illogically ignore reduction condition depth >= 3*ONE_PLY for predicted depth,
          // but fixing this made program slightly weaker.
          Depth predictedDepth = newDepth - reduction<PvNode>(depth, moveCount);
          futilityValue =  ss->staticEval + ss->evalMargin + futility_margin(predictedDepth, moveCount)
#ifdef GPSFISH
                         + H.gain(move.ptypeO(), to_sq(move)); // XXX
#else
                         + H.gain(pos.piece_moved(move), to_sq(move));
#endif

          if (futilityValue < beta)
          {
              if (SpNode)
                  sp->mutex.lock();

              continue;
          }

          // Prune moves with negative SEE at low depths
          if (   predictedDepth < 2 * ONE_PLY
              && pos.see_sign(move) < 0)
          {
              if (SpNode)
                  sp->mutex.lock();

              continue;
          }
      }

      // Check for legality only before to do the move
      if (!pos.pl_move_is_legal(move, ci.pinned))
      {
          moveCount--;
          continue;
      }

      pvMove = PvNode ? moveCount == 1 : false;
      ss->currentMove = move;
      if (!SpNode && !captureOrPromotion && playedMoveCount < 64)
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
      if (    depth > 3 * ONE_PLY
          && !pvMove
          && !captureOrPromotion
          && !dangerous
          &&  ss->killers[0] != move
          &&  ss->killers[1] != move)
      {
          ss->reduction = reduction<PvNode>(depth, moveCount);
          Depth d = std::max(newDepth - ss->reduction, ONE_PLY);
          alpha = SpNode ? sp->alpha : alpha;

          value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d);

          doFullDepthSearch = (value > alpha && ss->reduction != DEPTH_ZERO);
          ss->reduction = DEPTH_ZERO;
      }
      else
          doFullDepthSearch = !pvMove;

      // Step 16. Full depth search, when LMR is skipped or fails high
      if (doFullDepthSearch)
      {
          alpha = SpNode ? sp->alpha : alpha;
          value = newDepth < ONE_PLY ?
                          givesCheck ? -qsearch<NonPV,  true>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                                     : -qsearch<NonPV, false>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                                     : - search<NonPV>(pos, ss+1, -(alpha+1), -alpha, newDepth);
      }

      // Only for PV nodes do a full PV search on the first move or after a fail
      // high, in the latter case search only if value < beta, otherwise let the
      // parent node to fail low with value <= alpha and to try another move.
      if (PvNode && (pvMove || (value > alpha && (RootNode || value < beta))))
          value = newDepth < ONE_PLY ?
                          givesCheck ? -qsearch<PV,  true>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                     : -qsearch<PV, false>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
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
          sp->mutex.lock();
          bestValue = sp->bestValue;
          alpha = sp->alpha;
      }

      // Finished searching the move. If Signals.stop is true, the search
      // was aborted because the user interrupted the search or because we
      // ran out of time. In this case, the return value of the search cannot
      // be trusted, and we don't update the best move and/or PV.
      if (Signals.stop || thisThread->cutoff_occurred())
          return value; // To avoid returning VALUE_INFINITE

      if (RootNode)
      {
          RootMove& rm = *std::find(RootMoves.begin(), RootMoves.end(), move);

          // PV move or new best move ?
          if (pvMove || value > alpha)
          {
              rm.score = value;
              rm.extract_pv_from_tt(pos);

              // We record how often the best move has been changed in each
              // iteration. This information is used for time management: When
              // the best move changes frequently, we allocate some more time.
              if (!pvMove)
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
          if (SpNode) sp->bestValue = value;

          if (value > alpha)
          {
              bestMove = move;
              if (SpNode) sp->bestMove = move;

              if (PvNode && value < beta)
              {
                  alpha = value; // Update alpha here! Always alpha < beta
                  if (SpNode) sp->alpha = value;
              }
              else
              {
                  assert(value >= beta); // Fail high

                  if (SpNode) sp->cutoff = true;
                  break;
              }
          }
      }

      // Step 19. Check for splitting the search
      if (   !SpNode
          &&  depth >= Threads.min_split_depth()
          &&  bestValue < beta
          &&  Threads.available_slave_exists(thisThread))
      {
          bestValue = Threads.split<FakeSplit>(pos, ss, alpha, beta, bestValue, &bestMove,
                                               depth, threatMove, moveCount, mp, NT);
          if (bestValue >= beta)
              break;
      }
    }

    if (SpNode)
        return bestValue;

    // Step 20. Check for mate and stalemate
    // All legal moves have been searched and if there are no legal moves, it
    // must be mate or stalemate. Note that we can have a false positive in
    // case of Signals.stop or thread.cutoff_occurred() are set, but this is
    // harmless because return value is discarded anyhow in the parent nodes.
    // If we are in a singular extension search then return a fail low score.
    // A split node has at least one move, the one tried before to be splitted.
    if (!moveCount)
#ifdef GPSFISH
        return  (excludedMove != MOVE_NONE) ? alpha
              : (inCheck ? (move_is_pawn_drop((ss-1)->currentMove) ? mate_in(ss->ply) : mated_in(ss->ply) ) : VALUE_DRAW); // XXX : checking checkmate by pawn drop
#else
        return  excludedMove ? alpha
              : inCheck ? mated_in(ss->ply) : DrawValue[pos.side_to_move()];
#endif

    // If we have pruned all the moves without searching return a fail-low score
    if (bestValue == -VALUE_INFINITE)
    {
        assert(!playedMoveCount);

        bestValue = alpha;
    }

    if (bestValue >= beta) // Failed high
    {
        TT.store(posKey, value_to_tt(bestValue, ss->ply), BOUND_LOWER, depth,
                 bestMove, ss->staticEval, ss->evalMargin);

        if (!pos.is_capture_or_promotion(bestMove) && !inCheck)
        {
            if (bestMove != ss->killers[0])
            {
                ss->killers[1] = ss->killers[0];
                ss->killers[0] = bestMove;
            }

            // Increase history value of the cut-off move
            Value bonus = Value(int(depth) * int(depth));
            H.add(pos.piece_moved(bestMove), to_sq(bestMove), bonus);

            // Decrease history of all the other played non-capture moves
            for (int i = 0; i < playedMoveCount - 1; i++)
            {
                Move m = movesSearched[i];
                H.add(pos.piece_moved(m), to_sq(m), -bonus);
            }
        }
    }
    else // Failed low or PV search
        TT.store(posKey, value_to_tt(bestValue, ss->ply),
                 PvNode && bestMove != MOVE_NONE ? BOUND_EXACT : BOUND_UPPER,
                 depth, bestMove, ss->staticEval, ss->evalMargin);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // qsearch() is the quiescence search function, which is called by the main
  // search function when the remaining depth is zero (or, to be more precise,
  // less than ONE_PLY).

  template <NodeType NT, bool InCheck>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth) {

    const bool PvNode = (NT == PV);

    assert(NT == PV || NT == NonPV);
    assert(InCheck == pos.in_check());
    assert(alpha >= -VALUE_INFINITE && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(depth <= DEPTH_ZERO);

    StateInfo st;
    const TTEntry* tte;
    Key posKey;
    Move ttMove, move, bestMove;
    Value bestValue, value, ttValue, futilityValue, futilityBase, oldAlpha;
#ifdef GPSFISH
    bool givesCheck, evasionPrunable, fromNull;
#else
    bool givesCheck, enoughMaterial, evasionPrunable, fromNull;
#endif
    Depth ttDepth;

    // To flag BOUND_EXACT a node with eval above alpha and no available moves
    if (PvNode)
        oldAlpha = alpha;

    ss->currentMove = bestMove = MOVE_NONE;
    ss->ply = (ss-1)->ply + 1;
#ifdef GPSFISH
    fromNull = (ss-1)->currentMove.isPass();
#else
    fromNull = (ss-1)->currentMove == MOVE_NULL;
#endif

    // Check for an instant draw or maximum ply reached
    if (pos.is_draw<false, false>() || ss->ply > MAX_PLY)
        return DrawValue[pos.side_to_move()];

#ifdef GPSFISH
    if(can_capture_king(pos)){
        return mate_in(0);
    }
    if(!pos.osl_state.inCheck()
            && ImmediateCheckmate::hasCheckmateMove
            (pos.side_to_move(),pos.osl_state,bestMove)) {
        return mate_in(ss->ply);
    }
#endif

    // Transposition table lookup. At PV nodes, we don't use the TT for
    // pruning, but only for move ordering.
    posKey = pos.key();
    tte = TT.probe(posKey);
#ifdef GPSFISH
    ttMove = tte ? tte->move(pos) : MOVE_NONE;
#else
    ttMove = tte ? tte->move() : MOVE_NONE;
#endif
    ttValue = tte ? value_from_tt(tte->value(),ss->ply) : VALUE_NONE;

    // Decide whether or not to include checks, this fixes also the type of
    // TT entry depth that we are going to use. Note that in qsearch we use
    // only two types of depth in TT: DEPTH_QS_CHECKS or DEPTH_QS_NO_CHECKS.
    ttDepth = InCheck || depth >= DEPTH_QS_CHECKS ? DEPTH_QS_CHECKS
                                                  : DEPTH_QS_NO_CHECKS;
    if (   tte
        && tte->depth() >= ttDepth
        && ttValue != VALUE_NONE // Only in case of TT access race
        && (           PvNode ?  tte->type() == BOUND_EXACT
            : ttValue >= beta ? (tte->type() & BOUND_LOWER)
                              : (tte->type() & BOUND_UPPER)))
    {
        ss->currentMove = ttMove; // Can be MOVE_NONE
        return ttValue;
    }

    // Evaluate the position statically
    if (InCheck)
    {
        ss->staticEval = ss->evalMargin = VALUE_NONE;
        bestValue = futilityBase = -VALUE_INFINITE;
#ifndef GPSFISH
        enoughMaterial = false;
#endif
    }
    else
    {
        if (fromNull)
        {
            ss->staticEval = bestValue = -(ss-1)->staticEval;
            ss->evalMargin = VALUE_ZERO;
        }
        else if (tte)
        {
            assert(tte->static_value() != VALUE_NONE || Threads.size() > 1);

            ss->staticEval = bestValue = tte->static_value();
            ss->evalMargin = tte->static_value_margin();

            if (ss->staticEval == VALUE_NONE || ss->evalMargin == VALUE_NONE) // Due to a race
                ss->staticEval = bestValue = evaluate(pos, ss->evalMargin);
        }
        else
            ss->staticEval = bestValue = evaluate(pos, ss->evalMargin);

        // Stand pat. Return immediately if static value is at least beta
        if (bestValue >= beta)
        {
            if (!tte)
                TT.store(pos.key(), value_to_tt(bestValue, ss->ply), BOUND_LOWER,
                         DEPTH_NONE, MOVE_NONE, ss->staticEval, ss->evalMargin);

            return bestValue;
        }

        if (PvNode && bestValue > alpha)
            alpha = bestValue;

        futilityBase = ss->staticEval + ss->evalMargin + Value(128);
#ifndef GPSFISH
        enoughMaterial = pos.non_pawn_material(pos.side_to_move()) > RookValueMg;
#endif
    }

    // Initialize a MovePicker object for the current position, and prepare
    // to search the moves. Because the depth is <= 0 here, only captures,
    // queen promotions and checks (only if depth >= DEPTH_QS_CHECKS) will
    // be generated.
    MovePicker mp(pos, ttMove, depth, H, to_sq((ss-1)->currentMove));
    CheckInfo ci(pos);

    // Loop through the moves until no moves remain or a beta cutoff occurs
    while ((move = mp.next_move<false>()) != MOVE_NONE)
    {
      assert(is_ok(move));

#ifdef MOVE_STACK_REJECTIONS
      if(move_stack_rejections_probe(move,pos,ss,alpha)) continue;
#endif

      givesCheck = pos.move_gives_check(move, ci);

      // Futility pruning
      if (   !PvNode
          && !InCheck
          && !givesCheck
          && !fromNull
          &&  move != ttMove
#ifndef GPSFISH
          &&  enoughMaterial
          &&  type_of(move) != PROMOTION
          && !pos.is_passed_pawn_push(move))
#endif
         )
      {
#ifdef GPSFISH
          futilityValue =  futilityBase
                         + PieceValue[EG][pos.piece_on(to_sq(move))]
                         + (type_of(move) == PROMOTION ? promote_value_of_piece_on(pos.piece_on(from_sq(move))) : VALUE_ZERO);
#else
          futilityValue =  futilityBase
                         + PieceValue[EG][pos.piece_on(to_sq(move))]
                         + (type_of(move) == ENPASSANT ? PawnValueEg : VALUE_ZERO);
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
                       &&  InCheck
                       &&  bestValue > VALUE_MATED_IN_MAX_PLY
                       && !pos.is_capture(move)
#ifndef GPSFISH
                       && !pos.can_castle(pos.side_to_move())
#endif
                       ;

      // Don't search moves with negative SEE values
      if (   !PvNode
          && (!InCheck || evasionPrunable)
          &&  move != ttMove
#ifndef GPSFISH
          &&  type_of(move) != PROMOTION
#endif
          &&  pos.see_sign(move) < 0)
          continue;

      // Don't search useless checks
      if (   !PvNode
          && !InCheck
          &&  givesCheck
          &&  move != ttMove
          && !pos.is_capture_or_promotion(move)
          &&  ss->staticEval + PawnValueMg / 4 < beta
          && !check_is_dangerous(pos, move, futilityBase, beta))
          continue;

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
      value = givesCheck ? -qsearch<NT,  true>(pos, ss+1, -beta, -alpha, depth - ONE_PLY)
                         : -qsearch<NT, false>(pos, ss+1, -beta, -alpha, depth - ONE_PLY);
#ifdef GPSFISH
      --pos.eval;
      }
      );
#else
      pos.undo_move(move);
#endif

      assert(value > -VALUE_INFINITE && value < VALUE_INFINITE);

      // Check for new best move
      if (value > bestValue)
      {
          bestValue = value;

          if (value > alpha)
          {
              if (PvNode && value < beta) // Update alpha here! Always alpha < beta
              {
                  alpha = value;
                  bestMove = move;
              }
              else // Fail high
              {
                  TT.store(posKey, value_to_tt(value, ss->ply), BOUND_LOWER,
                           ttDepth, move, ss->staticEval, ss->evalMargin);

                  return value;
              }
          }
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
            if (solver.hasCheckmateMoveOfTurn(2,bestMove).isCheckmateSuccess()) {
                return mate_in(ss->ply+2);;
            }
        }
    }
#endif

    // All legal moves have been searched. A special case: If we're in check
    // and no legal moves were found, it is checkmate.
    if (InCheck && bestValue == -VALUE_INFINITE)
#ifdef GPSFISH
        return (move_is_pawn_drop((ss-1)->currentMove) ? mate_in(ss->ply) : mated_in(ss->ply)); // Plies to mate from the root
#else
        return mated_in(ss->ply); // Plies to mate from the root
#endif

    TT.store(posKey, value_to_tt(bestValue, ss->ply),
             PvNode && bestValue > oldAlpha ? BOUND_EXACT : BOUND_UPPER,
             ttDepth, bestMove, ss->staticEval, ss->evalMargin);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // value_to_tt() adjusts a mate score from "plies to mate from the root" to
  // "plies to mate from the current position". Non-mate scores are unchanged.
  // The function is called before storing a value to the transposition table.

  Value value_to_tt(Value v, int ply) {

    assert(v != VALUE_NONE);

    return  v >= VALUE_MATE_IN_MAX_PLY  ? v + ply
          : v <= VALUE_MATED_IN_MAX_PLY ? v - ply : v;
  }


  // value_from_tt() is the inverse of value_to_tt(): It adjusts a mate score
  // from the transposition table (where refers to the plies to mate/be mated
  // from current position) to "plies to mate/be mated from the root".

  Value value_from_tt(Value v, int ply) {

    return  v == VALUE_NONE             ? VALUE_NONE
          : v >= VALUE_MATE_IN_MAX_PLY  ? v - ply
          : v <= VALUE_MATED_IN_MAX_PLY ? v + ply : v;
  }


  // check_is_dangerous() tests if a checking move can be pruned in qsearch()

  bool check_is_dangerous(Position& pos, Move move, Value futilityBase, Value beta)
  {
#ifdef GPSFISH
    return false;
#else

    Piece pc = pos.piece_moved(move);
    Square from = from_sq(move);
    Square to = to_sq(move);
    Color them = ~pos.side_to_move();
    Square ksq = pos.king_square(them);
    Bitboard enemies = pos.pieces(them);
    Bitboard kingAtt = pos.attacks_from<KING>(ksq);
    Bitboard occ = pos.pieces() ^ from ^ ksq;
    Bitboard oldAtt = pos.attacks_from(pc, from, occ);
    Bitboard newAtt = pos.attacks_from(pc, to, occ);

    // Checks which give opponent's king at most one escape square are dangerous
    if (!more_than_one(kingAtt & ~(enemies | newAtt | to)))
        return true;

    // Queen contact check is very dangerous
    if (type_of(pc) == QUEEN && (kingAtt & to))
        return true;

    // Creating new double threats with checks is dangerous
    Bitboard b = (enemies ^ ksq) & newAtt & ~oldAtt;
    while (b)
    {
        // Note that here we generate illegal "double move"!
        if (futilityBase + PieceValue[EG][pos.piece_on(pop_lsb(&b))] >= beta)
            return true;
    }

    return false;
#endif
  }


  // yields_to_threat() tests whether the move at previous ply yields to the so
  // called threat move (the best move returned from a null search that fails
  // low). Here 'yields to' means that the move somehow made the threat possible
  // for instance if the moving piece is the same in both moves.

  bool yields_to_threat(const Position& pos, Move move, Move threat) {

    assert(is_ok(move));
    assert(is_ok(threat));
    assert(color_of(pos.piece_on(from_sq(threat))) == ~pos.side_to_move());

    Square mfrom = from_sq(move);
    Square mto = to_sq(move);
    Square tfrom = from_sq(threat);
    Square tto = to_sq(threat);

    // The piece is the same or threat's destination was vacated by the move
    if (mto == tfrom || tto == mfrom)
        return true;

    // Threat moves through the vacated square
#ifdef GPSFISH
    if(!tfrom.isPieceStand() && !mfrom.isPieceStand() &&
       Board_Table.getShortOffset(Offset32(tfrom,tto)) ==
       Board_Table.getShortOffset(Offset32(tfrom,mfrom)) &&
       abs((tfrom-tto).intValue())>abs((tfrom-mfrom).intValue())) return true;
#else
    if (between_bb(tfrom, tto) & mfrom)
      return true;
#endif

    // Threat's destination is defended by the move's piece
#ifdef GPSFISH
    osl::Piece pc=pos.osl_state.pieceAt(mto);
    if (pos.osl_state.hasEffectByPiece(pc,tto))
        return true;
#else
    Bitboard matt = pos.attacks_from(pos.piece_on(mto), mto, pos.pieces() ^ tfrom);
    if (matt & tto)
        return true;
#endif

    // Threat gives a discovered check through the move's checking piece
#ifdef GPSFISH
    pc=pos.osl_state.pieceAt(tto);
    if(pc.isPiece() && pos.osl_state.hasEffectByPiece(pc,tfrom) &&
       Ptype_Table.getEffect(pos.piece_on(mto),mto,pos.king_square(pos.side_to_move())).hasBlockableEffect() &&
       Board_Table.isBetweenSafe(tfrom,mto,pos.king_square(pos.side_to_move())) &&
       !Board_Table.isBetweenSafe(tto,mto,pos.king_square(pos.side_to_move())) &&
       pos.osl_state.pinOrOpen(pos.side_to_move()).test(pos.osl_state.pieceAt(mto).number()))
        return true;
#else
    if (matt & pos.king_square(pos.side_to_move()))
    {
        assert(between_bb(mto, pos.king_square(pos.side_to_move())) & tfrom);
        return true;
    }
#endif

    return false;
  }


  // prevents_threat() tests whether a move is able to defend against the so
  // called threat move (the best move returned from a null search that fails
  // low). In this case will not be pruned.

  bool prevents_threat(const Position& pos, Move move, Move threat) {

    assert(is_ok(move));
    assert(is_ok(threat));
    assert(!pos.is_capture_or_promotion(move));
#ifndef GPSFISH
    assert(!pos.is_passed_pawn_push(m));
    assert(!pos.is_passed_pawn_push(move));
#endif

    Square mfrom = from_sq(move);
    Square mto = to_sq(move);
    Square tfrom = from_sq(threat);
    Square tto = to_sq(threat);

    // Don't prune moves of the threatened piece
    if (mfrom == tto)
        return true;

    // If the threatened piece has value less than or equal to the value of the
    // threat piece, don't prune moves which defend it.
    if (    pos.is_capture(threat)
        && (   PieceValue[MG][pos.piece_on(tfrom)] >= PieceValue[MG][pos.piece_on(tto)]
#ifdef GPSFISH
            || type_of(pos.piece_on(tfrom)) == osl::KING))
#else
            || type_of(pos.piece_on(tfrom)) == KING))
#endif
    {
#ifdef GPSFISH
        if( pos.osl_state.hasEffectIf(move.ptypeO(), move.to(), tto) )
            return true;
#else
        // Update occupancy as if the piece and the threat are moving
        Bitboard occ = pos.pieces() ^ mfrom ^ mto ^ tfrom;
        Piece piece = pos.piece_on(mfrom);

        // The moved piece attacks the square 'tto' ?
        if (pos.attacks_from(piece, mto, occ) & tto)
            return true;

        // Scan for possible X-ray attackers behind the moved piece
        Bitboard xray =  (attacks_bb<  ROOK>(tto, occ) & pos.pieces(color_of(piece), QUEEN, ROOK))
                       | (attacks_bb<BISHOP>(tto, occ) & pos.pieces(color_of(piece), QUEEN, BISHOP));

        // Verify attackers are triggered by our move and not already existing
        if (xray && (xray ^ (xray & pos.attacks_from<QUEEN>(tto))))
            return true;
#endif
    }

    // Don't prune safe moves which block the threat path
#ifdef GPSFISH
    if (   !tfrom.isPieceStand() // XXX : should remove this ?
        && Board_Table.isBetweenSafe(mto,tfrom,tto)
        && pos.see_sign(move) >= 0)
#else
    if ((between_bb(tfrom, tto) & mto) && pos.see_sign(move) >= 0)
#endif
        return true;

    return false;
  }


  // When playing with strength handicap choose best move among the MultiPV set
  // using a statistical rule dependent on 'level'. Idea by Heinz van Saanen.

  Move Skill::pick_move() {

    static RKISS rk;

    // PRNG sequence should be not deterministic
    for (int i = Time::now() % 50; i > 0; i--)
        rk.rand<unsigned>();

    // RootMoves are already sorted by score in descending order
    int variance = std::min(RootMoves[0].score - RootMoves[PVSize - 1].score, PawnValueMg);
    int weakness = 120 - 2 * level;
    int max_s = -VALUE_INFINITE;
    best = MOVE_NONE;

    // Choose best move. For each move score we add two terms both dependent on
    // weakness, one deterministic and bigger for weaker moves, and one random,
    // then we choose the move with the resulting highest score.
    for (size_t i = 0; i < PVSize; i++)
    {
        int s = RootMoves[i].score;

        // Don't allow crazy blunders even at very low skills
        if (i > 0 && RootMoves[i-1].score > s + 2 * PawnValueMg)
            break;

        // This is our magic formula
        s += (  weakness * int(RootMoves[0].score - s)
              + variance * (rk.rand<unsigned>() % weakness)) / 128;

        if (s > max_s)
        {
            max_s = s;
            best = RootMoves[i].pv[0];
        }
    }
    return best;
  }


  // uci_pv() formats PV information according to UCI protocol. UCI requires
  // to send all the PV lines also if are still to be searched and so refer to
  // the previous search score.

  string uci_pv(const Position& pos, int depth, Value alpha, Value beta) {

    std::stringstream s;
    Time::point elaspsed = Time::now() - SearchTime + 1;
    size_t uciPVSize = std::min((size_t)Options["MultiPV"], RootMoves.size());
    int selDepth = 0;

    for (size_t i = 0; i < Threads.size(); i++)
        if (Threads[i].maxPly > selDepth)
            selDepth = Threads[i].maxPly;

    for (size_t i = 0; i < uciPVSize; i++)
    {
        bool updated = (i <= PVIdx);

        if (depth == 1 && !updated)
            continue;

        int d   = updated ? depth : depth - 1;
        Value v = updated ? RootMoves[i].score : RootMoves[i].prevScore;

        if (s.rdbuf()->in_avail()) // Not at first line
            s << "\n";

        s << "info depth " << d
          << " seldepth "  << selDepth
          << " score "     << (i == PVIdx ? score_to_uci(v, alpha, beta) : score_to_uci(v))
          << " nodes "     << pos.nodes_searched()
          << " nps "       << pos.nodes_searched() * 1000 / elaspsed
#ifdef GPSFISH
          //<< " time "      << (t > 0 ? t : 1)
          << " time "      << elaspsed
          << " hashfull "  << TT.get_hashfull()
#else
          << " time "      << elaspsed
          << " multipv "   << i + 1
#endif
          << " pv";

        for (size_t j = 0; RootMoves[i].pv[j] != MOVE_NONE; j++)
            s <<  " " << move_to_uci(RootMoves[i].pv[j], pos.is_chess960());
    }

    return s.str();
  }

} // namespace


/// RootMove::extract_pv_from_tt() builds a PV by adding moves from the TT table.
/// We consider also failing high nodes and not only BOUND_EXACT nodes so to
/// allow to always have a ponder move even when we fail high at root, and a
/// long PV to print that is important for position analysis.

#ifdef GPSFISH
void RootMove::extract_pv_from_tt_rec(Position& pos,int ply) {
  TTEntry* tte;

  if (   (tte = TT.probe(pos.key())) != NULL
          && tte->move(pos) != MOVE_NONE
          && pos.is_pseudo_legal(tte->move(pos))
          && pos.pl_move_is_legal(tte->move(pos), pos.pinned_pieces())
          && ply < MAX_PLY
          && (!pos.is_draw<true,true>() || ply < 2))
  {
      pv.push_back(tte->move(pos));
      StateInfo st;
      pos.do_undo_move(tte->move(pos),st,
              [&](osl::Square){
              assert(pos.is_ok());
              extract_pv_from_tt_rec(pos,ply+1);
      } );
  }

  pv.push_back(MOVE_NONE);
}
#endif

void RootMove::extract_pv_from_tt(Position& pos) {

#ifndef GPSFISH
  StateInfo state[MAX_PLY_PLUS_2], *st = state;
  TTEntry* tte;
  int ply = 0;
#endif
  Move m = pv[0];

  pv.clear();
#ifdef GPSFISH
  pv.push_back(m);

  StateInfo st;
  pos.do_undo_move(pv[0],st,
          [&](osl::Square){
          assert(pos.is_ok());
          extract_pv_from_tt_rec(pos,1);
          } );
#else

  do {
      pv.push_back(m);

      assert(pos.move_is_legal(pv[ply]));
      pos.do_move(pv[ply++], *st++);
      tte = TT.probe(pos.key());

  } while (   tte
           && pos.is_pseudo_legal(m = tte->move()) // Local copy, TT could change
           && pos.pl_move_is_legal(m, pos.pinned_pieces())
           && ply < MAX_PLY
           && (!pos.is_draw<true, true>() || ply < 2));

  pv.push_back(MOVE_NONE); // Must be zero-terminating

  while (ply) pos.undo_move(pv[--ply]);
#endif
}


/// RootMove::insert_pv_in_tt() is called at the end of a search iteration, and
/// inserts the PV back into the TT. This makes sure the old PV moves are searched
/// first, even if the old TT entries have been overwritten.

#ifdef GPSFISH
void RootMove::insert_pv_in_tt_rec(Position& pos,int ply) {
  TTEntry* tte;
  Key k;
  Value v, m = VALUE_NONE;
  k = pos.key();
  tte = TT.probe(k);

  // Don't overwrite existing correct entries
  if (!tte || tte->move(pos) != pv[ply])
  {
      v = (pos.in_check() ? VALUE_NONE : evaluate(pos, m));
      TT.store(k, VALUE_NONE, BOUND_NONE, DEPTH_NONE, pv[ply], v, m);
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
      } );
  }
}
#endif

void RootMove::insert_pv_in_tt(Position& pos) {

#ifdef GPSFISH
  insert_pv_in_tt_rec(pos,0);
#else

  StateInfo state[MAX_PLY_PLUS_2], *st = state;
  TTEntry* tte;
  int ply = 0;
  Value v, m;

  do {
      tte = TT.probe(pos.key());

      if (!tte || tte->move() != pv[ply]) // Don't overwrite correct entries
      {
          if (pos.in_check())
              v = m = VALUE_NONE;
          else
              v = evaluate(pos, m);

          TT.store(pos.key(), VALUE_NONE, BOUND_NONE, DEPTH_NONE, pv[ply], v, m);
      }

      assert(pos.move_is_legal(pv[ply]));
      pos.do_move(pv[ply++], *st++);

  } while (pv[ply] != MOVE_NONE);

  while (ply) pos.undo_move(pv[--ply]);
#endif
}

#ifdef GPSFISH
inline bool single_bit(uint64_t b) {
  return !(b & (b - 1));
}
#endif

/// Thread::idle_loop() is where the thread is parked when it has no work to do

void Thread::idle_loop() {

  // Pointer 'sp_master', if non-NULL, points to the active SplitPoint
  // object for which the thread is the master.
  const SplitPoint* sp_master = splitPointsCnt ? curSplitPoint : NULL;

  assert(!sp_master || (sp_master->master == this && is_searching));

  // If this thread is the master of a split point and all slaves have
  // finished their work at this split point, return from the idle loop.
  while (!sp_master || sp_master->slavesMask)
  {
      // If we are not searching, wait for a condition to be signaled
      // instead of wasting CPU time polling for work.
      while (   do_sleep
             || do_exit
             || (!is_searching && Threads.use_sleeping_threads()))
      {
          if (do_exit)
          {
              assert(!sp_master);
              return;
          }

          // Grab the lock to avoid races with Thread::wake_up()
          mutex.lock();

          // If we are master and all slaves have finished don't go to sleep
          if (sp_master && !sp_master->slavesMask)
          {
              mutex.unlock();
              break;
          }

          // Do sleep after retesting sleep conditions under lock protection, in
          // particular we need to avoid a deadlock in case a master thread has,
          // in the meanwhile, allocated us and sent the wake_up() call before we
          // had the chance to grab the lock.
          if (do_sleep || !is_searching)
              sleepCondition.wait(mutex);

          mutex.unlock();
      }

      // If this thread has been assigned work, launch a search
      if (is_searching)
      {
          assert(!do_sleep && !do_exit);

          Threads.mutex.lock();

          assert(is_searching);

          // Copy split point position and search stack and call search()
#ifdef MOVE_STACK_REJECTIONS
          SearchStack ss_base[MAX_PLY_PLUS_2];
          SplitPoint* tsp = threads[threadID].splitPoint;
          Position pos(*tsp->pos, threadID);
          int ply=tsp->ss->ply;
          assert(0< ply && ply+3<MAX_PLY_PLUS_2);
          for(int i=0;i<ply-1;i++)
              ss_base[i].currentMove=(tsp->ss-ply+i)->currentMove;
          SearchStack *ss= &ss_base[ply-1];
#else
          SplitPoint* sp = curSplitPoint;

          Threads.mutex.unlock();

          Stack ss[MAX_PLY_PLUS_2];
          Position pos(*sp->pos, this);
#endif

          memcpy(ss, sp->ss - 1, 4 * sizeof(Stack));
          (ss+1)->sp = sp;

#ifdef GPSFISH
          uint64_t es_base[(MAX_PLY_PLUS_2*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)];
          eval_t *es=(eval_t *)&es_base[0];
          assert(sp->pos->eval);
          es[0]= *(sp->pos->eval);
          pos.eval= &es[0];
#endif

          sp->mutex.lock();

          assert(sp->activePositions[idx] == NULL);

          sp->activePositions[idx] = &pos;

          if (sp->nodeType == Root)
              search<SplitPointRoot>(pos, ss+1, sp->alpha, sp->beta, sp->depth);
          else if (sp->nodeType == PV)
              search<SplitPointPV>(pos, ss+1, sp->alpha, sp->beta, sp->depth);
          else if (sp->nodeType == NonPV)
              search<SplitPointNonPV>(pos, ss+1, sp->alpha, sp->beta, sp->depth);
          else
              assert(false);

          assert(is_searching);

          is_searching = false;
          sp->activePositions[idx] = NULL;
          sp->slavesMask &= ~(1ULL << idx);
          sp->nodes += pos.nodes_searched();

          // Wake up master thread so to allow it to return from the idle loop in
          // case we are the last slave of the split point.
          if (    Threads.use_sleeping_threads()
              &&  this != sp->master
              && !sp->slavesMask)
          {
              assert(!sp->master->is_searching);
              sp->master->wake_up();
          }

          // After releasing the lock we cannot access anymore any SplitPoint
          // related data in a safe way becuase it could have been released under
          // our feet by the sp master. Also accessing other Thread objects is
          // unsafe because if we are exiting there is a chance are already freed.
          sp->mutex.unlock();
      }
  }
}

#ifdef GPSFISHONE
void do_checkmate(Position& pos, int mateTime){
    sync_cout << "checkmate notimplemented";
    return;
}
#else
void do_checkmate(Position& pos, int mateTime){
    Signals.stop=false;
    osl::state::NumEffectState state(pos.osl_state);
#if (! defined ALLOW_KING_ABSENCE)
    if (state.kingSquare(state.turn()).isPieceStand()) {
        sync_cout << "checkmate notimplemented";
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
        sync_cout << "info time " << static_cast<int>(elapsed*1000) << "nodes " << total+node_count
                  << "nps %d " << static_cast<int>(node_count/elapsed) << "hashfull " << static_cast<int>(memory*1000) << sync_endl;
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
        sync_cout << "checkmate timeout\n";
        return;
    }
    if (! result.isCheckmateSuccess()) {
        sync_cout << "checkmate nomate\n";
        return;
    }
    std::string msg = "checkmate";
    for (size_t i=0; i<pv.size(); ++i)
        msg += " " + move_to_uci(pv[i],false);
    sync_cout << msg << sync_endl;
}
#endif

#ifdef GPSFISH
void show_tree(Position &pos){
    show_tree_rec(pos);
}
#endif

/// check_time() is called by the timer thread when the timer triggers. It is
/// used to print debug info and, more important, to detect when we are out of
/// available time and so stop the search.

void check_time() {

  static Time::point lastInfoTime = Time::now();
  int64_t nodes = 0; // Workaround silly 'uninitialized' gcc warning

  if (Time::now() - lastInfoTime >= 1000)
  {
      lastInfoTime = Time::now();
      dbg_print();
  }

  if (Limits.ponder)
      return;

  if (Limits.nodes)
  {
      Threads.mutex.lock();

      nodes = RootPos.nodes_searched();

      // Loop across all split points and sum accumulated SplitPoint nodes plus
      // all the currently active slaves positions.
      for (size_t i = 0; i < Threads.size(); i++)
          for (int j = 0; j < Threads[i].splitPointsCnt; j++)
          {
              SplitPoint& sp = Threads[i].splitPoints[j];

              sp.mutex.lock();

              nodes += sp.nodes;
              Bitboard sm = sp.slavesMask;
              while (sm)
              {
                  Position* pos = sp.activePositions[pop_lsb(&sm)];
                  nodes += pos ? pos->nodes_searched() : 0;
              }

              sp.mutex.unlock();
          }

      Threads.mutex.unlock();
  }

  Time::point elapsed = Time::now() - SearchTime;
  bool stillAtFirstMove =    Signals.firstRootMove
                         && !Signals.failedLowAtRoot
                         &&  elapsed > TimeMgr.available_time();

  bool noMoreTime =   elapsed > TimeMgr.maximum_time() - 2 * TimerResolution
                   || stillAtFirstMove;

  if (   (Limits.use_time_management() && noMoreTime)
      || (Limits.movetime && elapsed >= Limits.movetime)
      || (Limits.nodes && nodes >= Limits.nodes))
      Signals.stop = true;
}
