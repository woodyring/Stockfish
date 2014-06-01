/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2014 Marco Costalba, Joona Kiiski, Tord Romstad

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
#include <cfloat>
#include <cmath>
#include <cstring>
#include <iostream>
#include <sstream>

#include "book.h"
#include "evaluate.h"
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
#include "osl/bits/boardTable.h"
using osl::Board_Table;
#include "osl/bits/ptypeTable.h"
using osl::Ptype_Table;
#include "osl/bits/offset32.h"
using osl::Offset32;
#include "osl/checkmate/immediateCheckmate.h"
#include "osl/checkmate/immediateCheckmate.tcc"
#include "osl/checkmate/fixedDepthSearcher.h"
#include "osl/checkmate/fixedDepthSearcher.tcc"
//#include "osl/checkmate/dfpn.h"
using osl::checkmate::ImmediateCheckmate;
using std::string;
#include "osl/enterKing.h"
#include "osl/hashKey.h"
#endif
#ifdef MOVE_STACK_REJECTIONS
#include "osl/search/moveStackRejections.h"
#endif

#ifdef GPSFISH
# define GPSFISH_CHECKMATE3
# define GPSFISH_CHECKMATE3_QUIESCE
# define GPSFISH_DFPN
# define GPSFISH_FIX // some commit from sf_4 to sf_dd prevent to find checkmate move
#endif

#ifdef GPSFISH_DFPN
#include <boost/scoped_ptr.hpp>
#include "osl/misc/milliSeconds.h"
#include "osl/checkmate/dfpn.h"
#include "osl/checkmate/dfpnParallel.h"
#endif

namespace Search {

  volatile SignalsType Signals;
  LimitsType Limits;
  std::vector<RootMove> RootMoves;
  Position RootPos;
  Color RootColor;
  Time::point SearchTime;
  StateStackPtr SetupStates;
  Value Contempt[2]; // [bestValue > VALUE_DRAW]
}

using std::string;
using Eval::evaluate;
using namespace Search;

namespace {

  // Set to true to force running with one thread. Used for debugging
  const bool FakeSplit = false;

  // Different node types, used as template parameter
  enum NodeType { Root, PV, NonPV, SplitPointRoot, SplitPointPV, SplitPointNonPV };

  // Dynamic razoring margin based on depth
  inline Value razor_margin(Depth d) { return Value(512 + 16 * d); }

  // Futility lookup tables (initialized at startup) and their access functions
  int FutilityMoveCounts[2][32]; // [improving][depth]

  inline Value futility_margin(Depth d) {
    return Value(100 * d);
  }

  // Reduction lookup tables (initialized at startup) and their access function
  int8_t Reductions[2][2][64][64]; // [pv][improving][depth][moveNumber]

  template <bool PvNode> inline Depth reduction(bool i, Depth d, int mn) {

    return (Depth) Reductions[PvNode][i][std::min(int(d) / ONE_PLY, 63)][std::min(mn, 63)];
  }

  size_t MultiPV, PVIdx;
  TimeManager TimeMgr;
  double BestMoveChanges;
#ifdef GPSFISH
  osl::CArray<Value,COLOR_NB> DrawValue;
#else
  Value DrawValue[COLOR_NB];
#endif
  HistoryStats History;
  GainsStats Gains;
  MovesStats Countermoves, Followupmoves;

  template <NodeType NT>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth, bool cutNode);

  template <NodeType NT, bool InCheck>
  Value qsearch(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth);

  void id_loop(Position& pos);
  Value value_to_tt(Value v, int ply);
  Value value_from_tt(Value v, int ply);
  void update_stats(Position& pos, Stack* ss, Move move, Depth depth, Move* quiets, int quietsCnt);
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
    const TTEntry* tte = TT.probe(pos.key());
    StateInfo st;
    if ( tte != NULL ) {
      std::cerr << "tte->value=" << tte->value() << std::endl;
      std::cerr << "tte->bound=" << tte->bound() << std::endl;
      std::cerr << "tte->depth=" << tte->depth() << std::endl;
      Move m=tte->move(pos);
      int dummy;
      if(m != MOVE_NONE
              && pos.pseudo_legal(m)
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
  for (hd = 1; hd < 64; ++hd) for (mc = 1; mc < 64; ++mc)
  {
      double    pvRed = 0.00 + log(double(hd)) * log(double(mc)) / 3.00;
      double nonPVRed = 0.33 + log(double(hd)) * log(double(mc)) / 2.25;
      Reductions[1][1][hd][mc] = (int8_t) (   pvRed >= 1.0 ? floor(   pvRed * int(ONE_PLY)) : 0);
      Reductions[0][1][hd][mc] = (int8_t) (nonPVRed >= 1.0 ? floor(nonPVRed * int(ONE_PLY)) : 0);

      Reductions[1][0][hd][mc] = Reductions[1][1][hd][mc];
      Reductions[0][0][hd][mc] = Reductions[0][1][hd][mc];

      if (Reductions[0][0][hd][mc] > 2 * ONE_PLY)
          Reductions[0][0][hd][mc] += ONE_PLY;

      else if (Reductions[0][0][hd][mc] > 1 * ONE_PLY)
          Reductions[0][0][hd][mc] += ONE_PLY / 2;
  }

  // Init futility move count array
  for (d = 0; d < 32; ++d)
  {
      FutilityMoveCounts[0][d] = int(2.4 + 0.222 * pow(d + 0.00, 1.8));
      FutilityMoveCounts[1][d] = int(3.0 + 0.300 * pow(d + 0.98, 1.8));
  }
}


/// Search::perft() is our utility to verify move generation. All the leaf nodes
/// up to the given depth are generated and counted and the sum returned.

static uint64_t perft(Position& pos, Depth depth) {

  StateInfo st;
  uint64_t cnt = 0;
  CheckInfo ci(pos);
  const bool leaf = depth == 2 * ONE_PLY;

#ifdef GPSFISH
  for (MoveList<LEGAL> it(pos); *it!=MOVE_NONE; ++it)
#else
  for (MoveList<LEGAL> it(pos); *it; ++it)
#endif
  {
#ifdef GPSFISH
      pos.do_undo_move(*it,st,
              [&](osl::Square){
              assert(pos.is_ok());
#else
      pos.do_move(*it, st, ci, pos.gives_check(*it, ci));
#endif
      cnt += leaf ? MoveList<LEGAL>(pos).size() : ::perft(pos, depth - ONE_PLY);
#ifdef GPSFISH
      } );
#else
      pos.undo_move(*it);
#endif
  }
  return cnt;
}

uint64_t Search::perft(Position& pos, Depth depth) {
  return depth > ONE_PLY ? ::perft(pos, depth) : MoveList<LEGAL>(pos).size();
}

/// Search::think() is the external interface to Stockfish's search, and is
/// called by the main thread when the program receives the UCI 'go' command. It
/// searches from RootPos and at the end prints the "bestmove" to output.

void Search::think() {

  static PolyglotBook book; // Defined static to initialize the PRNG only once

  RootColor = RootPos.side_to_move();
  TimeMgr.init(Limits, RootPos.game_ply(), RootColor);

  DrawValue[0] = DrawValue[1] = VALUE_DRAW;
  Contempt[0] =  Options["Contempt Factor"] * PawnValueEg / 100; // From centipawns
  Contempt[1] = (Options["Contempt Factor"] + 12) * PawnValueEg / 100;

  if (RootMoves.empty())
  {
      RootMoves.push_back(MOVE_NONE);
      sync_cout << "info depth 0 score "
                << score_to_uci(RootPos.checkers() ? -VALUE_MATE : VALUE_DRAW)
                << sync_endl;

      goto finalize;
  }

  if (Options["OwnBook"] && !Limits.infinite && !Limits.mate)
  {
      Move bookMove = book.probe(RootPos, Options["Book File"], Options["Best Book Move"]);

      if (bookMove && std::count(RootMoves.begin(), RootMoves.end(), bookMove))
      {
          std::swap(RootMoves[0], *std::find(RootMoves.begin(), RootMoves.end(), bookMove));
#ifdef GPSFISH
          RootMoves[0].score = (Value)0;
#endif
          goto finalize;
      }
  }

  if (Options["Write Search Log"])
  {
      Log log(Options["Search Log Filename"]);
      log << "\nSearching: "  << RootPos.fen()
          << "\ninfinite: "   << Limits.infinite
          << " ponder: "      << Limits.ponder
          << " time: "        << Limits.time[RootColor]
          << " increment: "   << Limits.inc[RootColor]
          << " moves to go: " << Limits.movestogo
          << "\n" << std::endl;
  }

  // Reset the threads, still sleeping: will wake up at split time
  for (size_t i = 0; i < Threads.size(); ++i)
      Threads[i]->maxPly = 0;

  Threads.sleepWhileIdle = Options["Idle Threads Sleep"];
  Threads.timer->run = true;
  Threads.timer->notify_one(); // Wake up the recurring timer

  id_loop(RootPos); // Let's start searching !

  Threads.timer->run = false; // Stop the timer
  Threads.sleepWhileIdle = true; // Send idle threads to sleep

  if (Options["Write Search Log"])
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

  // When search is stopped this info is not printed
  sync_cout << "info nodes " << RootPos.nodes_searched()
            << " time " << Time::now() - SearchTime + 1 << sync_endl;

  // When we reach the maximum depth, we can arrive here without a raise of
  // Signals.stop. However, if we are pondering or in an infinite search,
  // the UCI protocol states that we shouldn't print the best move before the
  // GUI sends a "stop" or "ponderhit" command. We therefore simply wait here
  // until the GUI sends one of those commands (which also raises Signals.stop).
  if (!Signals.stop && (Limits.ponder || Limits.infinite))
  {
      Signals.stopOnPonderhit = true;
      RootPos.this_thread()->wait_for(Signals.stop);
  }

  //if( Options["Resign"] )
  {
      //sync_cout << "info string score " << RootMoves[0].score << " resign " <<  -Options["Resign"] << sync_endl;
      if( RootMoves[0].score/2 <= -Options["Resign"] ) {
          RootMoves[0].pv[0] = MOVE_NONE;
      }
  }

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
        const TTEntry* tte = TT.probe(pos.key());
        if (tte && tte->bound() == BOUND_EXACT
                && tte->depth() >= CheckmateDepth) {
            Value v = value_from_tt(tte->value(), 0);
            if (v >= VALUE_MATE_IN_MAX_PLY || v < VALUE_MATED_IN_MAX_PLY)
                return Move();		// mate or mated
        }

        osl::PathEncoding path(pos.osl_state.turn());
        osl::Move checkmate_move;
        osl::NumEffectState& state = pos.osl_state;
        std::vector<osl::Move> pv;
        osl::checkmate::ProofDisproof result
            = dfpn[playerToIndex(state.turn())].
            hasCheckmateMove(state, osl::HashKey(state), path, nodes,
                    checkmate_move, Move(), &pv);
        if (result.isCheckmateSuccess()) {
            TT.store(pos.key(), mate_in(pv.size()),
                    BOUND_EXACT, CheckmateDepth, checkmate_move, VALUE_NONE);
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
            if (next.first < last && pos->pl_move_is_legal(moves[next.first])
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

    Stack stack[MAX_PLY_PLUS_6], *ss = stack+2; // To allow referencing (ss-2)
    int depth;
    Value bestValue, alpha, beta, delta;

#ifdef GPSFISH
    uint64_t es_base[(MAX_PLY_PLUS_6*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)]
#ifdef __GNUC__
      __attribute__((aligned(16)))
#endif
	;
    eval_t *es=(eval_t *)&es_base[0];
#endif

    std::memset(ss-2, 0, 5 * sizeof(Stack));
#ifdef GPSFISH
    (ss-1)->currentMove = osl::Move::PASS(pos.side_to_move()); // Hack to skip update_gains
#else
    (ss-1)->currentMove = MOVE_NULL; // Hack to skip update gains
#endif

    depth = 0;
    BestMoveChanges = 0;
    bestValue = delta = alpha = -VALUE_INFINITE;
    beta = VALUE_INFINITE;

    TT.new_search();
    History.clear();
    Gains.clear();
    Countermoves.clear();
    Followupmoves.clear();

    MultiPV = Options["MultiPV"];
    Skill skill(Options["Skill Level"]);

    // Do we have to play with skill handicap? In this case enable MultiPV search
    // that we will use behind the scenes to retrieve a set of possible moves.
    if (skill.enabled() && MultiPV < 4)
        MultiPV = 4;

    MultiPV = std::min(MultiPV, RootMoves.size());

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
        // Age out PV variability metric
        BestMoveChanges *= 0.5;

        // Save the last iteration's scores before first PV line is searched and
        // all the move scores except the (new) PV are set to -VALUE_INFINITE.
        for (size_t i = 0; i < RootMoves.size(); ++i)
            RootMoves[i].prevScore = RootMoves[i].score;

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
        for (PVIdx = 0; PVIdx < MultiPV && !Signals.stop; ++PVIdx)
        {
            // Reset aspiration window starting size
            if (depth >= 5)
            {
                delta = Value(16);
                alpha = std::max(RootMoves[PVIdx].prevScore - delta,-VALUE_INFINITE);
                beta  = std::min(RootMoves[PVIdx].prevScore + delta, VALUE_INFINITE);
            }

            // Start with a small aspiration window and, in the case of a fail
            // high/low, re-search with a bigger window until we're not failing
            // high/low anymore.
            while (true)
            {
                bestValue = search<Root>(pos, ss, alpha, beta, depth * ONE_PLY, false);

                DrawValue[ RootColor] = VALUE_DRAW - Contempt[bestValue > VALUE_DRAW];
                DrawValue[~RootColor] = VALUE_DRAW + Contempt[bestValue > VALUE_DRAW];

                // Bring the best move to the front. It is critical that sorting
                // is done with a stable algorithm because all the values but the
                // first and eventually the new best one are set to -VALUE_INFINITE
                // and we want to keep the same order for all the moves except the
                // new PV that goes to the front. Note that in case of MultiPV
                // search the already searched PV lines are preserved.
                std::stable_sort(RootMoves.begin() + PVIdx, RootMoves.end());

                // Write PV back to transposition table in case the relevant
                // entries have been overwritten during the search.
                for (size_t i = 0; i <= PVIdx; ++i)
                    RootMoves[i].insert_pv_in_tt(pos);

                // If search has been stopped break immediately. Sorting and
                // writing PV back to TT is safe because RootMoves is still
                // valid, although it refers to previous iteration.
                if (Signals.stop)
                    break;

                // When failing high/low give some update (without cluttering
                // the UI) before a re-search.
                if (  (bestValue <= alpha || bestValue >= beta)
                    && Time::now() - SearchTime > 3000)
                    sync_cout << uci_pv(pos, depth, alpha, beta) << sync_endl;

                // In case of failing low/high increase aspiration window and
                // re-search, otherwise exit the loop.
                if (bestValue <= alpha)
                {
                    alpha = std::max(bestValue - delta, -VALUE_INFINITE);

                    Signals.failedLowAtRoot = true;
                    Signals.stopOnPonderhit = false;
                }
                else if (bestValue >= beta)
                    beta = std::min(bestValue + delta, VALUE_INFINITE);

                else
                    break;

                delta += delta / 2;

                assert(alpha >= -VALUE_INFINITE && beta <= VALUE_INFINITE);
            }

            // Sort the PV lines searched so far and update the GUI
            std::stable_sort(RootMoves.begin(), RootMoves.begin() + PVIdx + 1);

            if (PVIdx + 1 == MultiPV || Time::now() - SearchTime > 3000)
                sync_cout << uci_pv(pos, depth, alpha, beta) << sync_endl;
        }

        // If skill levels are enabled and time is up, pick a sub-optimal best move
        if (skill.enabled() && skill.time_to_pick(depth))
            skill.pick_move();

        if (Options["Write Search Log"])
        {
            RootMove& rm = RootMoves[0];
            if (skill.best != MOVE_NONE)
                rm = *std::find(RootMoves.begin(), RootMoves.end(), skill.best);

            Log log(Options["Search Log Filename"]);
            log << pretty_pv(pos, depth, rm.score, Time::now() - SearchTime, &rm.pv[0])
                << std::endl;
        }

        // Have we found a "mate in x"?
        if (   Limits.mate
            && bestValue >= VALUE_MATE_IN_MAX_PLY
            && VALUE_MATE - bestValue <= 2 * Limits.mate)
            Signals.stop = true;

        // Do we have time for the next iteration? Can we stop searching now?
        if (Limits.use_time_management() && !Signals.stop && !Signals.stopOnPonderhit)
        {
            // Take some extra time if the best move has changed
            if (depth > 4 && depth < 50 &&  MultiPV == 1)
                TimeMgr.pv_instability(BestMoveChanges);

            // Stop the search if only one legal move is available or all
            // of the available time has been used.
            if (   RootMoves.size() == 1
                || Time::now() - SearchTime > TimeMgr.available_time())
            {
                // If we are allowed to ponder do not stop the search now but
                // keep pondering until the GUI sends "ponderhit" or "stop".
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
  // search, and searched the first move before splitting, so we don't have to
  // repeat all this work again. We also don't need to store anything to the hash
  // table here: This is taken care of after we return from the split point.

  template <NodeType NT>
  Value search(Position& pos, Stack* ss, Value alpha, Value beta, Depth depth, bool cutNode) {

    const bool PvNode   = (NT == PV || NT == Root || NT == SplitPointPV || NT == SplitPointRoot);
    const bool SpNode   = (NT == SplitPointPV || NT == SplitPointNonPV || NT == SplitPointRoot);
    const bool RootNode = (NT == Root || NT == SplitPointRoot);

    assert(-VALUE_INFINITE <= alpha && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(depth > DEPTH_ZERO);

    Move quietsSearched[64];
    StateInfo st;
    const TTEntry *tte;
    SplitPoint* splitPoint;
    Key posKey;
    Move ttMove, move, excludedMove, bestMove;
    Depth ext, newDepth, predictedDepth;
    Value bestValue, value, ttValue, eval, nullValue, futilityValue;
    bool inCheck, givesCheck, pvMove, singularExtensionNode, improving;
    bool captureOrPromotion, dangerous, doFullDepthSearch;
    int moveCount, quietCount;

    // Step 1. Initialize node
    Thread* thisThread = pos.this_thread();

#ifdef GPSFISH
    int repeat_check = 0;

    if(can_capture_king(pos)){
        return mate_in(0);
    }
#endif

    inCheck = pos.checkers();

    if (SpNode)
    {
        splitPoint = ss->splitPoint;
        bestMove   = splitPoint->bestMove;
        bestValue  = splitPoint->bestValue;
        tte = NULL;
        ttMove = excludedMove = MOVE_NONE;
        ttValue = VALUE_NONE;

        assert(splitPoint->bestValue > -VALUE_INFINITE && splitPoint->moveCount > 0);

        goto moves_loop;
    }

    moveCount = quietCount = 0;
    bestValue = -VALUE_INFINITE;
    ss->currentMove = ss->ttMove = (ss+1)->excludedMove = bestMove = MOVE_NONE;
    ss->ply = (ss-1)->ply + 1;
    (ss+1)->skipNullMove = false; (ss+1)->reduction = DEPTH_ZERO;
    (ss+2)->killers[0] = (ss+2)->killers[1] = MOVE_NONE;

    // Used to send selDepth info to GUI
    if (PvNode && thisThread->maxPly < ss->ply)
        thisThread->maxPly = ss->ply;

    if (!RootNode)
    {
        // Step 2. Check for aborted search and immediate draw
#ifdef GPSFISH
        if (Signals.stop || pos.is_draw(repeat_check) || ss->ply > MAX_PLY)
#else
        if (Signals.stop || pos.is_draw() || ss->ply > MAX_PLY)
#endif
            return ss->ply > MAX_PLY && !inCheck ? evaluate(pos) : DrawValue[pos.side_to_move()];

#ifdef GPSFISH
        if(repeat_check<0)
            return mated_in(ss->ply);
        else if(repeat_check>0)
            return mate_in(ss->ply);
        else if(osl::EnterKing::canDeclareWin(pos.osl_state))
            return mate_in(ss->ply+1);

        if (!ss->checkmateTested) {
            ss->checkmateTested = true;
            if(!pos.osl_state.inCheck()
                    && ImmediateCheckmate::hasCheckmateMove(pos.side_to_move(),pos.osl_state,bestMove)) {
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
                    if (solver.hasCheckmateMoveOfTurn(2,bestMove).isCheckmateSuccess()) {
                        return mate_in(ss->ply+2);
                    }
                }
            }
#  endif
        }
#endif // GPSFISH

        // Step 3. Mate distance pruning. Even if we mate at the next move our score
        // would be at best mate_in(ss->ply+1), but if alpha is already bigger because
        // a shorter mate was found upward in the tree then there is no need to search
        // because we will never beat the current alpha. Same logic but with reversed
        // signs applies also in the opposite condition of being mated instead of giving
        // mate. In this case return a fail-high score.
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
    ss->ttMove = ttMove = RootNode ? RootMoves[PVIdx].pv[0] : tte ? tte->move(pos) : MOVE_NONE;
#else
    ss->ttMove = ttMove = RootNode ? RootMoves[PVIdx].pv[0] : tte ? tte->move() : MOVE_NONE;
#endif
    ttValue = tte ? value_from_tt(tte->value(), ss->ply) : VALUE_NONE;

    // At PV nodes we check for exact scores, whilst at non-PV nodes we check for
    // a fail high/low. The biggest advantage to probing at PV nodes is to have a
    // smooth experience in analysis mode. We don't probe at Root nodes otherwise
    // we should also update RootMoveList to avoid bogus output.
    if (   !RootNode
        && tte
        && tte->depth() >= depth
        && ttValue != VALUE_NONE // Only in case of TT access race
        && (           PvNode ?  tte->bound() == BOUND_EXACT
            : ttValue >= beta ? (tte->bound() &  BOUND_LOWER)
                              : (tte->bound() &  BOUND_UPPER)))
    {
        ss->currentMove = ttMove; // Can be MOVE_NONE

        // If ttMove is quiet, update killers, history, counter move and followup move on TT hit
        if (ttValue >= beta && ttMove && !pos.capture_or_promotion(ttMove) && !inCheck)
            update_stats(pos, ss, ttMove, depth, NULL, 0);

        return ttValue;
    }

    // Step 5. Evaluate the position statically and update parent's gain statistics
    if (inCheck)
    {
        ss->staticEval = eval = VALUE_NONE;
        goto moves_loop;
    }

    else if (tte)
    {
        // Never assume anything on values stored in TT
        if ((ss->staticEval = eval = tte->eval_value()) == VALUE_NONE)
            eval = ss->staticEval = evaluate(pos);

        // Can ttValue be used as a better position evaluation?
        if (ttValue != VALUE_NONE)
            if (tte->bound() & (ttValue > eval ? BOUND_LOWER : BOUND_UPPER))
                eval = ttValue;
    }
    else
    {
        eval = ss->staticEval = evaluate(pos);
        TT.store(posKey, VALUE_NONE, BOUND_NONE, DEPTH_NONE, MOVE_NONE, ss->staticEval);
    }

    if (   !pos.captured_piece_type()
        &&  ss->staticEval != VALUE_NONE
        && (ss-1)->staticEval != VALUE_NONE
#ifdef GPSFISH
        &&!(move = (ss-1)->currentMove).isPass()
#else
        && (move = (ss-1)->currentMove) != MOVE_NULL
#endif
        &&  type_of(move) == NORMAL)
    {
        Square to = to_sq(move);
#ifdef GPSFISH
        Gains.update(move.ptypeO(), to, -(ss-1)->staticEval - ss->staticEval);
#else
        Gains.update(pos.piece_on(to), to, -(ss-1)->staticEval - ss->staticEval);
#endif
    }

    // Step 6. Razoring (skipped when in check)
    if (   !PvNode
        &&  depth < 4 * ONE_PLY
        &&  eval + razor_margin(depth) <= alpha
        &&  ttMove == MOVE_NONE
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY
#ifndef GPSFISH
        && !pos.pawn_on_7th(pos.side_to_move()))
#endif
      )
    {
        Value ralpha = alpha - razor_margin(depth);
        Value v = qsearch<NonPV, false>(pos, ss, ralpha, ralpha+1, DEPTH_ZERO);
        if (v <= ralpha)
            return v;
    }

    // Step 7. Futility pruning: child node (skipped when in check)
    if (   !PvNode
        && !ss->skipNullMove
        &&  depth < 7 * ONE_PLY
        &&  eval - futility_margin(depth) >= beta
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY
        &&  abs(eval) < VALUE_KNOWN_WIN
#ifndef GPSFISH
        &&  pos.non_pawn_material(pos.side_to_move())
#endif
	   )
        return eval - futility_margin(depth);

    // Step 8. Null move search with verification search (is omitted in PV nodes)
    if (   !PvNode
        && !ss->skipNullMove
        &&  depth >= 2 * ONE_PLY
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

        assert(eval - beta >= 0);

        // Null move dynamic reduction based on depth and value
        Depth R =  3 * ONE_PLY
                 + depth / 4
                 + int(eval - beta) / PawnValueMg * ONE_PLY;

#ifdef GPSFISH
        pos.do_undo_null_move(st,
                [&](osl::Square){
                *(pos.eval+1)= *(pos.eval);
                pos.eval++;
                pos.eval->update(pos.osl_state,ss->currentMove);
#else
        pos.do_null_move(st);
#endif
        (ss+1)->skipNullMove = true;
        nullValue = depth-R < ONE_PLY ? -qsearch<NonPV, false>(pos, ss+1, -beta, -beta+1, DEPTH_ZERO)
                                      : - search<NonPV>(pos, ss+1, -beta, -beta+1, depth-R, !cutNode);
        (ss+1)->skipNullMove = false;
#ifdef GPSFISH
	    --pos.eval;
	  }
	  );
#else
        pos.undo_null_move();
#endif

        if (nullValue >= beta)
        {
            // Do not return unproven mate scores
            if (nullValue >= VALUE_MATE_IN_MAX_PLY)
                nullValue = beta;

            if (depth < 12 * ONE_PLY)
                return nullValue;

            // Do verification search at high depths
            ss->skipNullMove = true;
            Value v = depth-R < ONE_PLY ? qsearch<NonPV, false>(pos, ss, beta-1, beta, DEPTH_ZERO)
                                        :  search<NonPV>(pos, ss, beta-1, beta, depth-R, false);
            ss->skipNullMove = false;

            if (v >= beta)
                return nullValue;
        }
    }

    // Step 9. ProbCut (skipped when in check)
    // If we have a very good capture (i.e. SEE > seeValues[captured_piece_type])
    // and a reduced search returns a value much above beta, we can (almost) safely
    // prune the previous move.
    if (   !PvNode
        &&  depth >= 5 * ONE_PLY
        && !ss->skipNullMove
        &&  abs(beta) < VALUE_MATE_IN_MAX_PLY)
    {
        Value rbeta = std::min(beta + 200, VALUE_INFINITE);
        Depth rdepth = depth - 4 * ONE_PLY;

        assert(rdepth >= ONE_PLY);
        assert((ss-1)->currentMove != MOVE_NONE);
        assert((ss-1)->currentMove != MOVE_NULL);

        MovePicker mp(pos, ttMove, History, pos.captured_piece_type());
        CheckInfo ci(pos);

        while ((move = mp.next_move<false>()) != MOVE_NONE)
            if (pos.legal(move, ci.pinned))
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
                pos.do_move(move, st, ci, pos.gives_check(move, ci));
#endif
                value = -search<NonPV>(pos, ss+1, -rbeta, -rbeta+1, rdepth, !cutNode);
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

    // Step 10. Internal iterative deepening (skipped when in check)
    if (    depth >= (PvNode ? 5 * ONE_PLY : 8 * ONE_PLY)
        && !ttMove
        && (PvNode || ss->staticEval + 256 >= beta))
    {
        Depth d = depth - 2 * ONE_PLY - (PvNode ? DEPTH_ZERO : depth / 4);

        ss->skipNullMove = true;
        search<PvNode ? PV : NonPV>(pos, ss, alpha, beta, d, true);
        ss->skipNullMove = false;

        tte = TT.probe(posKey);
#ifdef GPSFISH
        ttMove = tte ? tte->move(pos) : MOVE_NONE;
#else
        ttMove = tte ? tte->move() : MOVE_NONE;
#endif
    }

moves_loop: // When in check and at SpNode search starts from here

    Square prevMoveSq = to_sq((ss-1)->currentMove);
#ifdef GPSFISH
    Move countermoves[] = { Countermoves[pos.piece_on(prevMoveSq)][prevMoveSq.index()].first,
                            Countermoves[pos.piece_on(prevMoveSq)][prevMoveSq.index()].second };
#else
    Move countermoves[] = { Countermoves[pos.piece_on(prevMoveSq)][prevMoveSq].first,
                            Countermoves[pos.piece_on(prevMoveSq)][prevMoveSq].second };
#endif

    Square prevOwnMoveSq = to_sq((ss-2)->currentMove);
#ifdef GPSFISH
    Move followupmoves[] = { Followupmoves[pos.piece_on(prevOwnMoveSq)][prevOwnMoveSq.index()].first,
                             Followupmoves[pos.piece_on(prevOwnMoveSq)][prevOwnMoveSq.index()].second };
#else
    Move followupmoves[] = { Followupmoves[pos.piece_on(prevOwnMoveSq)][prevOwnMoveSq].first,
                             Followupmoves[pos.piece_on(prevOwnMoveSq)][prevOwnMoveSq].second };
#endif

    MovePicker mp(pos, ttMove, depth, History, countermoves, followupmoves, ss);
    CheckInfo ci(pos);
    value = bestValue; // Workaround a bogus 'uninitialized' warning under gcc
    improving =   ss->staticEval >= (ss-2)->staticEval
               || ss->staticEval == VALUE_NONE
               ||(ss-2)->staticEval == VALUE_NONE;

    singularExtensionNode =   !RootNode
                           && !SpNode
#ifdef GPSFISH_FIX
                           &&  depth >= (PvNode ? 6 * ONE_PLY : 8 * ONE_PLY)
#else
                           &&  depth >= 8 * ONE_PLY
#endif
                           &&  ttMove != MOVE_NONE
#ifdef GPSFISH
                           && excludedMove==MOVE_NONE // Recursive singular search is not allowed
#else
                           && !excludedMove // Recursive singular search is not allowed
#endif
                           && (tte->bound() & BOUND_LOWER)
                           &&  tte->depth() >= depth - 3 * ONE_PLY;

    // Step 11. Loop through moves
    // Loop through all pseudo-legal moves until no moves remain or a beta cutoff occurs
    while ((move = mp.next_move<SpNode>()) != MOVE_NONE)
    {
      assert(is_ok(move));

      if (move == excludedMove)
          continue;

      // At root obey the "searchmoves" option and skip moves not listed in Root
      // Move List. As a consequence any illegal move is also skipped. In MultiPV
      // mode we also skip PV moves which have been already searched.
      if (RootNode && !std::count(RootMoves.begin() + PVIdx, RootMoves.end(), move))
          continue;

      if (SpNode)
      {
          // Shared counter cannot be decremented later if the move turns out to be illegal
          if (!pos.legal(move, ci.pinned))
              continue;

          moveCount = ++splitPoint->moveCount;
          splitPoint->mutex.unlock();
      }
      else
          ++moveCount;
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

#ifndef GPSFISH
          if (thisThread == Threads.main() && Time::now() - SearchTime > 3000)
              sync_cout << "info depth " << depth / ONE_PLY
                        << " currmove " << move_to_uci(move, pos.is_chess960())
                        << " currmovenumber " << moveCount + PVIdx << sync_endl;
#endif
      }

      ext = DEPTH_ZERO;
      captureOrPromotion = pos.capture_or_promotion(move);
#ifdef GPSFISH
      givesCheck = pos.gives_check(move, ci);
      dangerous =   givesCheck; // XXX : add other condition ?
#else
      givesCheck =  type_of(move) == NORMAL && !ci.dcCandidates
                  ? ci.checkSq[type_of(pos.piece_on(from_sq(move)))] & to_sq(move)
                  : pos.gives_check(move, ci);

      dangerous =   givesCheck
                 || type_of(move) != NORMAL
                 || pos.advanced_pawn_push(move);
#endif

#ifdef GPSFISH_FIX
      // Step 12. Extend checks and, in PV nodes, also dangerous moves
      if (PvNode && dangerous)
          ext = ONE_PLY;

      else if (givesCheck && pos.see_sign(move) >= 0)
          ext = inCheck || ss->staticEval <= alpha ? ONE_PLY : ONE_PLY / 2;
#else
      // Step 12. Extend checks
      if (givesCheck && pos.see_sign(move) >= VALUE_ZERO)
          ext = ONE_PLY;
#endif

      // Singular extension search. If all moves but one fail low on a search of
      // (alpha-s, beta-s), and just one fails high on (alpha, beta), then that move
      // is singular and should be extended. To verify this we do a reduced search
      // on all the other moves but the ttMove and if the result is lower than
      // ttValue minus a margin then we extend the ttMove.
      if (    singularExtensionNode
          &&  move == ttMove
          && !ext
          &&  pos.legal(move, ci.pinned)
          &&  abs(ttValue) < VALUE_KNOWN_WIN)
      {
          assert(ttValue != VALUE_NONE);

          Value rBeta = ttValue - int(depth);
          ss->excludedMove = move;
          ss->skipNullMove = true;
          value = search<NonPV>(pos, ss, rBeta - 1, rBeta, depth / 2, cutNode);
          ss->skipNullMove = false;
          ss->excludedMove = MOVE_NONE;

          if (value < rBeta)
              ext = ONE_PLY;
      }

      // Update the current move (this must be done after singular extension search)
      newDepth = depth - ONE_PLY + ext;

      // Step 13. Pruning at shallow depth (exclude PV nodes)
      if (   !PvNode
          && !captureOrPromotion
          && !inCheck
          && !dangerous
       /* &&  move != ttMove Already implicit in the next condition */
          &&  bestValue > VALUE_MATED_IN_MAX_PLY)
      {
          // Move count based pruning
          if (   depth < 16 * ONE_PLY
              && moveCount >= FutilityMoveCounts[improving][depth] )
          {
              if (SpNode)
                  splitPoint->mutex.lock();

              continue;
          }

          predictedDepth = newDepth - reduction<PvNode>(improving, depth, moveCount);

          // Futility pruning: parent node
          if (predictedDepth < 7 * ONE_PLY)
          {
              futilityValue = ss->staticEval + futility_margin(predictedDepth)
#ifdef GPSFISH
                            + 128 + Gains[pos.moved_piece(move)][to_sq(move).index()];
#else
                            + 128 + Gains[pos.moved_piece(move)][to_sq(move)];
#endif

              if (futilityValue <= alpha)
              {
                  bestValue = std::max(bestValue, futilityValue);

                  if (SpNode)
                  {
                      splitPoint->mutex.lock();
                      if (bestValue > splitPoint->bestValue)
                          splitPoint->bestValue = bestValue;
                  }
                  continue;
              }
          }

          // Prune moves with negative SEE at low depths
          if (predictedDepth < 4 * ONE_PLY && pos.see_sign(move) < VALUE_ZERO)
          {
              if (SpNode)
                  splitPoint->mutex.lock();

              continue;
          }
      }

      // Check for legality just before making the move
      if (!RootNode && !SpNode && !pos.legal(move, ci.pinned))
      {
          moveCount--;
          continue;
      }

      pvMove = PvNode && moveCount == 1;
      ss->currentMove = move;
      if (!SpNode && !captureOrPromotion && quietCount < 64)
          quietsSearched[quietCount++] = move;

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

      // Step 15. Reduced depth search (LMR). If the move fails high it will be
      // re-searched at full depth.
      if (    depth >= 3 * ONE_PLY
          && !pvMove
          && !captureOrPromotion
#ifdef GPSFISH_FIX
          && !dangerous
#endif
          &&  move != ttMove
          &&  move != ss->killers[0]
          &&  move != ss->killers[1])
      {
          ss->reduction = reduction<PvNode>(improving, depth, moveCount);

          if (!PvNode && cutNode)
              ss->reduction += ONE_PLY;

#ifdef GPSFISH
          else if (History[pos.piece_on(to_sq(move))][to_sq(move).index()] < 0)
#else
          else if (History[pos.piece_on(to_sq(move))][to_sq(move)] < 0)
#endif
              ss->reduction += ONE_PLY / 2;

          if (move == countermoves[0] || move == countermoves[1])
              ss->reduction = std::max(DEPTH_ZERO, ss->reduction - ONE_PLY);

          Depth d = std::max(newDepth - ss->reduction, ONE_PLY);
          if (SpNode)
              alpha = splitPoint->alpha;

          value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d, true);

          // Research at intermediate depth if reduction is very high
          if (value > alpha && ss->reduction >= 4 * ONE_PLY)
          {
              Depth d2 = std::max(newDepth - 2 * ONE_PLY, ONE_PLY);
              value = -search<NonPV>(pos, ss+1, -(alpha+1), -alpha, d2, true);
          }

          doFullDepthSearch = (value > alpha && ss->reduction != DEPTH_ZERO);
          ss->reduction = DEPTH_ZERO;
      }
      else
          doFullDepthSearch = !pvMove;

      // Step 16. Full depth search, when LMR is skipped or fails high
      if (doFullDepthSearch)
      {
          if (SpNode)
              alpha = splitPoint->alpha;

          value = newDepth < ONE_PLY ?
                          givesCheck ? -qsearch<NonPV,  true>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                                     : -qsearch<NonPV, false>(pos, ss+1, -(alpha+1), -alpha, DEPTH_ZERO)
                                     : - search<NonPV>(pos, ss+1, -(alpha+1), -alpha, newDepth, !cutNode);
      }

      // For PV nodes only, do a full PV search on the first move or after a fail
      // high (in the latter case search only if value < beta), otherwise let the
      // parent node fail low with value <= alpha and to try another move.
      if (PvNode && (pvMove || (value > alpha && (RootNode || value < beta))))
          value = newDepth < ONE_PLY ?
                          givesCheck ? -qsearch<PV,  true>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                     : -qsearch<PV, false>(pos, ss+1, -beta, -alpha, DEPTH_ZERO)
                                     : - search<PV>(pos, ss+1, -beta, -alpha, newDepth, false);

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
          splitPoint->mutex.lock();
          bestValue = splitPoint->bestValue;
          alpha = splitPoint->alpha;
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
                  ++BestMoveChanges;

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
              // All other moves but the PV are set to the lowest value: this is
              // not a problem when sorting because the sort is stable and the
              // move position in the list is preserved - just the PV is pushed up.
              rm.score = -VALUE_INFINITE;
      }

      if (value > bestValue)
      {
          bestValue = SpNode ? splitPoint->bestValue = value : value;

          if (value > alpha)
          {
              bestMove = SpNode ? splitPoint->bestMove = move : move;

              if (PvNode && value < beta) // Update alpha! Always alpha < beta
                  alpha = SpNode ? splitPoint->alpha = value : value;
              else
              {
                  assert(value >= beta); // Fail high

                  if (SpNode)
                      splitPoint->cutoff = true;

                  break;
              }
          }
      }

      // Step 19. Check for splitting the search
      if (   !SpNode
          &&  depth >= Threads.minimumSplitDepth
          &&  Threads.available_slave(thisThread)
          &&  thisThread->splitPointsSize < MAX_SPLITPOINTS_PER_THREAD)
      {
          assert(bestValue < beta);

          thisThread->split<FakeSplit>(pos, ss, alpha, beta, &bestValue, &bestMove,
                                       depth, moveCount, &mp, NT, cutNode);
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
    // A split node has at least one move - the one tried before to be split.
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
        bestValue = alpha;

    TT.store(posKey, value_to_tt(bestValue, ss->ply),
             bestValue >= beta  ? BOUND_LOWER :
#ifdef GPSFISH
             PvNode && (bestMove != MOVE_NONE) ? BOUND_EXACT : BOUND_UPPER,
#else
             PvNode && bestMove ? BOUND_EXACT : BOUND_UPPER,
#endif
             depth, bestMove, ss->staticEval);

    // Quiet best move: update killers, history, countermoves and followupmoves
    if (bestValue >= beta && !pos.capture_or_promotion(bestMove) && !inCheck)
        update_stats(pos, ss, bestMove, depth, quietsSearched, quietCount - 1);

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
    assert(InCheck == !!pos.checkers());
    assert(alpha >= -VALUE_INFINITE && alpha < beta && beta <= VALUE_INFINITE);
    assert(PvNode || (alpha == beta - 1));
    assert(depth <= DEPTH_ZERO);

    StateInfo st;
    const TTEntry* tte;
    Key posKey;
    Move ttMove, move, bestMove;
    Value bestValue, value, ttValue, futilityValue, futilityBase, oldAlpha;
    bool givesCheck, evasionPrunable;
    Depth ttDepth;

    // To flag BOUND_EXACT a node with eval above alpha and no available moves
    if (PvNode)
        oldAlpha = alpha;

    ss->currentMove = bestMove = MOVE_NONE;
    ss->ply = (ss-1)->ply + 1;

    // Check for an instant draw or if the maximum ply has been reached
    if (pos.is_draw() || ss->ply > MAX_PLY)
        return ss->ply > MAX_PLY && !InCheck ? evaluate(pos) : DrawValue[pos.side_to_move()];

    // Decide whether or not to include checks: this fixes also the type of
    // TT entry depth that we are going to use. Note that in qsearch we use
    // only two types of depth in TT: DEPTH_QS_CHECKS or DEPTH_QS_NO_CHECKS.
    ttDepth = InCheck || depth >= DEPTH_QS_CHECKS ? DEPTH_QS_CHECKS
                                                  : DEPTH_QS_NO_CHECKS;

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

    // Transposition table lookup
    posKey = pos.key();
    tte = TT.probe(posKey);
#ifdef GPSFISH
    ttMove = tte ? tte->move(pos) : MOVE_NONE;
#else
    ttMove = tte ? tte->move() : MOVE_NONE;
#endif
    ttValue = tte ? value_from_tt(tte->value(),ss->ply) : VALUE_NONE;

    if (   tte
        && tte->depth() >= ttDepth
        && ttValue != VALUE_NONE // Only in case of TT access race
        && (           PvNode ?  tte->bound() == BOUND_EXACT
            : ttValue >= beta ? (tte->bound() &  BOUND_LOWER)
                              : (tte->bound() &  BOUND_UPPER)))
    {
        ss->currentMove = ttMove; // Can be MOVE_NONE
        return ttValue;
    }

    // Evaluate the position statically
    if (InCheck)
    {
        ss->staticEval = VALUE_NONE;
        bestValue = futilityBase = -VALUE_INFINITE;
    }
    else
    {
        if (tte)
        {
            // Never assume anything on values stored in TT
            if ((ss->staticEval = bestValue = tte->eval_value()) == VALUE_NONE)
                ss->staticEval = bestValue = evaluate(pos);

            // Can ttValue be used as a better position evaluation?
            if (ttValue != VALUE_NONE)
                if (tte->bound() & (ttValue > bestValue ? BOUND_LOWER : BOUND_UPPER))
                    bestValue = ttValue;
        }
        else
            ss->staticEval = bestValue = evaluate(pos);

        // Stand pat. Return immediately if static value is at least beta
        if (bestValue >= beta)
        {
            if (!tte)
                TT.store(pos.key(), value_to_tt(bestValue, ss->ply), BOUND_LOWER,
                         DEPTH_NONE, MOVE_NONE, ss->staticEval);

            return bestValue;
        }

        if (PvNode && bestValue > alpha)
            alpha = bestValue;

        futilityBase = bestValue + 128;
    }

    // Initialize a MovePicker object for the current position, and prepare
    // to search the moves. Because the depth is <= 0 here, only captures,
    // queen promotions and checks (only if depth >= DEPTH_QS_CHECKS) will
    // be generated.
    MovePicker mp(pos, ttMove, depth, History, to_sq((ss-1)->currentMove));
    CheckInfo ci(pos);

    // Loop through the moves until no moves remain or a beta cutoff occurs
    while ((move = mp.next_move<false>()) != MOVE_NONE)
    {
      assert(is_ok(move));

#ifdef MOVE_STACK_REJECTIONS
      if(move_stack_rejections_probe(move,pos,ss,alpha)) continue;
#endif

#ifdef GPSFISH
      givesCheck = pos.gives_check(move, ci);
#else
      givesCheck =  type_of(move) == NORMAL && !ci.dcCandidates
                  ? ci.checkSq[type_of(pos.piece_on(from_sq(move)))] & to_sq(move)
                  : pos.gives_check(move, ci);
#endif

      // Futility pruning
      if (   !PvNode
          && !InCheck
          && !givesCheck
          &&  move != ttMove
          &&  futilityBase > -VALUE_KNOWN_WIN
#ifndef GPSFISH
          && !pos.advanced_pawn_push(move)
#endif
         )
      {
#ifdef GPSFISH
          futilityValue =  futilityBase
                         + PieceValue[EG][pos.piece_on(to_sq(move))]
                         + (type_of(move) == PROMOTION ? promote_value_of_piece_on(pos.piece_on(from_sq(move))) : VALUE_ZERO); // XXX : need condition ?
#else
          assert(type_of(move) != ENPASSANT); // Due to !pos.advanced_pawn_push

          futilityValue = futilityBase + PieceValue[EG][pos.piece_on(to_sq(move))];
#endif

          if (futilityValue < beta)
          {
              bestValue = std::max(bestValue, futilityValue);
              continue;
          }

          if (futilityBase < beta && pos.see(move) <= VALUE_ZERO)
          {
              bestValue = std::max(bestValue, futilityBase);
              continue;
          }
      }

      // Detect non-capture evasions that are candidates to be pruned
      evasionPrunable =    InCheck
                       &&  bestValue > VALUE_MATED_IN_MAX_PLY
                       && !pos.capture(move)
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
          &&  pos.see_sign(move) < VALUE_ZERO)
          continue;

      // Check for legality just before making the move
      if (!pos.legal(move, ci.pinned))
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
                           ttDepth, move, ss->staticEval);

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
                return mate_in(ss->ply+2);
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
             ttDepth, bestMove, ss->staticEval);

    assert(bestValue > -VALUE_INFINITE && bestValue < VALUE_INFINITE);

    return bestValue;
  }


  // value_to_tt() adjusts a mate score from "plies to mate from the root" to
  // "plies to mate from the current position". Non-mate scores are unchanged.
  // The function is called before storing a value in the transposition table.

  Value value_to_tt(Value v, int ply) {

    assert(v != VALUE_NONE);

    return  v >= VALUE_MATE_IN_MAX_PLY  ? v + ply
          : v <= VALUE_MATED_IN_MAX_PLY ? v - ply : v;
  }


  // value_from_tt() is the inverse of value_to_tt(): It adjusts a mate score
  // from the transposition table (which refers to the plies to mate/be mated
  // from current position) to "plies to mate/be mated from the root".

  Value value_from_tt(Value v, int ply) {

    return  v == VALUE_NONE             ? VALUE_NONE
          : v >= VALUE_MATE_IN_MAX_PLY  ? v - ply
          : v <= VALUE_MATED_IN_MAX_PLY ? v + ply : v;
  }


  // update_stats() updates killers, history, countermoves and followupmoves stats after a fail-high
  // of a quiet move.

  void update_stats(Position& pos, Stack* ss, Move move, Depth depth, Move* quiets, int quietsCnt) {

    if (ss->killers[0] != move)
    {
        ss->killers[1] = ss->killers[0];
        ss->killers[0] = move;
    }

    // Increase history value of the cut-off move and decrease all the other
    // played quiet moves.
    Value bonus = Value(int(depth) * int(depth));
    History.update(pos.moved_piece(move), to_sq(move), bonus);
    for (int i = 0; i < quietsCnt; ++i)
    {
        Move m = quiets[i];
        History.update(pos.moved_piece(m), to_sq(m), -bonus);
    }

    if (is_ok((ss-1)->currentMove))
    {
        Square prevMoveSq = to_sq((ss-1)->currentMove);
        Countermoves.update(pos.piece_on(prevMoveSq), prevMoveSq, move);
    }

    if (is_ok((ss-2)->currentMove) && (ss-1)->currentMove == (ss-1)->ttMove)
    {
        Square prevOwnMoveSq = to_sq((ss-2)->currentMove);
        Followupmoves.update(pos.piece_on(prevOwnMoveSq), prevOwnMoveSq, move);
    }
  }


  // When playing with a strength handicap, choose best move among the MultiPV
  // set using a statistical rule dependent on 'level'. Idea by Heinz van Saanen.

  Move Skill::pick_move() {

    static RKISS rk;

    // PRNG sequence should be not deterministic
    for (int i = Time::now() % 50; i > 0; --i)
        rk.rand<unsigned>();

    // RootMoves are already sorted by score in descending order
    int variance = std::min(RootMoves[0].score - RootMoves[MultiPV - 1].score, PawnValueMg);
    int weakness = 120 - 2 * level;
    int max_s = -VALUE_INFINITE;
    best = MOVE_NONE;

    // Choose best move. For each move score we add two terms both dependent on
    // weakness. One deterministic and bigger for weaker moves, and one random,
    // then we choose the move with the resulting highest score.
    for (size_t i = 0; i < MultiPV; ++i)
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


  // uci_pv() formats PV information according to the UCI protocol. UCI
  // requires that all (if any) unsearched PV lines are sent using a previous
  // search score.

  string uci_pv(const Position& pos, int depth, Value alpha, Value beta) {

    std::stringstream ss;
    Time::point elapsed = Time::now() - SearchTime + 1;
    size_t uciPVSize = std::min((size_t)Options["MultiPV"], RootMoves.size());
    int selDepth = 0;

    for (size_t i = 0; i < Threads.size(); ++i)
        if (Threads[i]->maxPly > selDepth)
            selDepth = Threads[i]->maxPly;

    for (size_t i = 0; i < uciPVSize; ++i)
    {
        bool updated = (i <= PVIdx);

        if (depth == 1 && !updated)
            continue;

        int d   = updated ? depth : depth - 1;
        Value v = updated ? RootMoves[i].score : RootMoves[i].prevScore;

        if (ss.rdbuf()->in_avail()) // Not at first line
            ss << "\n";

        ss << "info depth " << d
           << " seldepth "  << selDepth
           << " score "     << (i == PVIdx ? score_to_uci(v, alpha, beta) : score_to_uci(v))
           << " nodes "     << pos.nodes_searched()
           << " nps "       << pos.nodes_searched() * 1000 / elapsed
           << " time "      << elapsed
#ifdef GPSFISH
           << " hashfull "  << TT.get_hashfull()
#endif
           << " multipv "   << i + 1
           << " pv";

        for (size_t j = 0; RootMoves[i].pv[j] != MOVE_NONE; ++j)
            ss << " " << move_to_uci(RootMoves[i].pv[j], pos.is_chess960());
    }

    return ss.str();
  }

} // namespace


/// RootMove::extract_pv_from_tt() builds a PV by adding moves from the TT table.
/// We also consider both failing high nodes and BOUND_EXACT nodes here to
/// ensure that we have a ponder move even when we fail high at root. This
/// results in a long PV to print that is important for position analysis.

#ifdef GPSFISH
void RootMove::extract_pv_from_tt_rec(Position& pos,int ply)
{
  const TTEntry* tte = TT.probe(pos.key());

  if ( tte != NULL
          && tte->move(pos) != MOVE_NONE
          && pos.pseudo_legal(tte->move(pos))
          && pos.legal(tte->move(pos), pos.pinned_pieces(pos.side_to_move()))
          && ply < MAX_PLY
          && (!pos.is_draw() || ply < 2))
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
  StateInfo state[MAX_PLY_PLUS_6], *st = state;
  const TTEntry* tte;
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

      assert(MoveList<LEGAL>(pos).contains(pv[ply]));

      pos.do_move(pv[ply++], *st++);
      tte = TT.probe(pos.key());

  } while (   tte
           && pos.pseudo_legal(m = tte->move()) // Local copy, TT could change
           && pos.legal(m, pos.pinned_pieces(pos.side_to_move()))
           && ply < MAX_PLY
           && (!pos.is_draw() || ply < 2));

  pv.push_back(MOVE_NONE); // Must be zero-terminating

  while (ply) pos.undo_move(pv[--ply]);
#endif
}


/// RootMove::insert_pv_in_tt() is called at the end of a search iteration, and
/// inserts the PV back into the TT. This makes sure the old PV moves are searched
/// first, even if the old TT entries have been overwritten.

#ifdef GPSFISH
void RootMove::insert_pv_in_tt_rec(Position& pos,int ply)
{
  const TTEntry* tte = TT.probe(pos.key());

  if (!tte || tte->move(pos) != pv[ply]) // Don't overwrite correct entries
      TT.store(pos.key(), VALUE_NONE, BOUND_NONE, DEPTH_NONE, pv[ply], VALUE_NONE);

  if (pv[ply+1] != MOVE_NONE) {
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

  StateInfo state[MAX_PLY_PLUS_6], *st = state;
  const TTEntry* tte;
  int ply = 0;

  do {
      tte = TT.probe(pos.key());

      if (!tte || tte->move() != pv[ply]) // Don't overwrite correct entries
          TT.store(pos.key(), VALUE_NONE, BOUND_NONE, DEPTH_NONE, pv[ply], VALUE_NONE);

      assert(MoveList<LEGAL>(pos).contains(pv[ply]));

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

  // Pointer 'this_sp' is not null only if we are called from split(), and not
  // at the thread creation. This means we are the split point's master.
  SplitPoint* this_sp = splitPointsSize ? activeSplitPoint : NULL;

  assert(!this_sp || (this_sp->masterThread == this && searching));

  while (true)
  {
      // If we are not searching, wait for a condition to be signaled instead of
      // wasting CPU time polling for work.
      while ((!searching && Threads.sleepWhileIdle) || exit)
      {
          if (exit)
          {
              assert(!this_sp);
              return;
          }

          // Grab the lock to avoid races with Thread::notify_one()
          mutex.lock();

          // If we are master and all slaves have finished then exit idle_loop
          if (this_sp && this_sp->slavesMask.none())
          {
              mutex.unlock();
              break;
          }

          // Do sleep after retesting sleep conditions under lock protection. In
          // particular we need to avoid a deadlock in case a master thread has,
          // in the meanwhile, allocated us and sent the notify_one() call before
          // we had the chance to grab the lock.
          if (!searching && !exit)
              sleepCondition.wait(mutex);

          mutex.unlock();
      }

      // If this thread has been assigned work, launch a search
      if (searching)
      {
          assert(!exit);

          Threads.mutex.lock();

          assert(searching);
          assert(activeSplitPoint);

          // Copy split point position and search stack and call search()
#ifdef MOVE_STACK_REJECTIONS
          SearchStack ss_base[MAX_PLY_PLUS_6];
          SplitPoint* tsp = threads[threadID].splitPoint;
          Position pos(*tsp->pos, threadID);
          int ply=tsp->ss->ply;
          assert(0< ply && ply+3<MAX_PLY_PLUS_6);
          for(int i=0;i<ply-1;i++)
              ss_base[i].currentMove=(tsp->ss-ply+i)->currentMove;
          SearchStack *ss= &ss_base[ply-1];
#else
          SplitPoint* sp = activeSplitPoint;

          Threads.mutex.unlock();

          Stack stack[MAX_PLY_PLUS_6], *ss = stack+2; // To allow referencing (ss-2)
          Position pos(*sp->pos, this);
#endif

          std::memcpy(ss-2, sp->ss-2, 5 * sizeof(Stack));
          ss->splitPoint = sp;

#ifdef GPSFISH
          uint64_t es_base[(MAX_PLY_PLUS_6*sizeof(eval_t)+sizeof(uint64_t)-1)/sizeof(uint64_t)];
          eval_t *es=(eval_t *)&es_base[0];
          assert(sp->pos->eval);
          es[0]= *(sp->pos->eval);
          pos.eval= &es[0];
#endif

          sp->mutex.lock();

          assert(activePosition == NULL);

          activePosition = &pos;

          switch (sp->nodeType) {
          case Root:
              search<SplitPointRoot>(pos, ss, sp->alpha, sp->beta, sp->depth, sp->cutNode);
              break;
          case PV:
              search<SplitPointPV>(pos, ss, sp->alpha, sp->beta, sp->depth, sp->cutNode);
              break;
          case NonPV:
              search<SplitPointNonPV>(pos, ss, sp->alpha, sp->beta, sp->depth, sp->cutNode);
              break;
          default:
              assert(false);
          }

          assert(searching);

          searching = false;
          activePosition = NULL;
          sp->slavesMask.reset(idx);
          sp->nodes += pos.nodes_searched();

          // Wake up the master thread so to allow it to return from the idle
          // loop in case we are the last slave of the split point.
          if (    Threads.sleepWhileIdle
              &&  this != sp->masterThread
              &&  sp->slavesMask.none())
          {
              assert(!sp->masterThread->searching);
              sp->masterThread->notify_one();
          }

          // After releasing the lock we can't access any SplitPoint related data
          // in a safe way because it could have been released under our feet by
          // the sp master. Also accessing other Thread objects is unsafe because
          // if we are exiting there is a chance that they are already freed.
          sp->mutex.unlock();
      }

      // If this thread is the master of a split point and all slaves have finished
      // their work at this split point, return from the idle loop.
      if (this_sp && this_sp->slavesMask.none())
      {
          this_sp->mutex.lock();
          bool finished = this_sp->slavesMask.none(); // Retest under lock protection
          this_sp->mutex.unlock();
          if (finished)
              return;
      }
  }
}

#ifndef GPSFISH_DFPN
void do_checkmate(const Position& pos, int mateTime){
    sync_cout << "checkmate notimplemented";
    return;
}
#else
void do_checkmate(const Position& pos, int mateTime){
    Signals.stop=false;
    osl::NumEffectState state(pos.osl_state);
#if (! defined ALLOW_KING_ABSENCE)
    if (state.kingSquare(state.turn()).isPieceStand()) {
        sync_cout << "checkmate notimplemented";
        return;
    }
#endif
    osl::checkmate::DfpnTable table(state.turn());
    const osl::PathEncoding path(state.turn());
    osl::Move checkmate_move;
    std::vector<osl::Move> pv;
    osl::checkmate::ProofDisproof result;
    osl::checkmate::Dfpn dfpn;
    dfpn.setTable(&table);
    double seconds=(double)mateTime/1000.0;
    osl::misc::time_point start = osl::misc::clock::now();
    size_t step = 100000, total = 0;
    double scale = 1.0;
    for (size_t limit = step; true; limit = static_cast<size_t>(step*scale)) {
        result = dfpn.
            hasCheckmateMove(state, osl::hash::HashKey(state), path, limit, checkmate_move, Move(), &pv);
        double elapsed = osl::misc::elapsedSeconds(start) + 1;
        double memory = osl::OslConfig::memoryUseRatio();
        uint64_t node_count = dfpn.nodeCount();
        sync_cout << "info time " << static_cast<int>(elapsed*1000) << " nodes " << total+node_count
                  << " nps " << static_cast<int>(node_count/elapsed) << " hashfull " << static_cast<int>(memory*1000) << sync_endl;
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
/// used to print debug info and, more importantly, to detect when we are out of
/// available time and thus stop the search.

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
      // all the currently active positions nodes.
      for (size_t i = 0; i < Threads.size(); ++i)
          for (int j = 0; j < Threads[i]->splitPointsSize; ++j)
          {
              SplitPoint& sp = Threads[i]->splitPoints[j];

              sp.mutex.lock();

              nodes += sp.nodes;

              for (size_t idx = 0; idx < Threads.size(); ++idx)
                  if (sp.slavesMask.test(idx) && Threads[idx]->activePosition)
                      nodes += Threads[idx]->activePosition->nodes_searched();

              sp.mutex.unlock();
          }

      Threads.mutex.unlock();
  }

  Time::point elapsed = Time::now() - SearchTime;
  bool stillAtFirstMove =    Signals.firstRootMove
                         && !Signals.failedLowAtRoot
                         &&  elapsed > TimeMgr.available_time() * 75 / 100;

  bool noMoreTime =   elapsed > TimeMgr.maximum_time() - 2 * TimerThread::Resolution
                   || stillAtFirstMove;

  if (   (Limits.use_time_management() && noMoreTime)
      || (Limits.movetime && elapsed >= Limits.movetime)
      || (Limits.nodes && nodes >= Limits.nodes))
      Signals.stop = true;
}
