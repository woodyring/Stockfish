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

#include <cassert>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "evaluate.h"
#include "misc.h"
#include "move.h"
#include "position.h"
#include "search.h"
#include "thread.h"
#include "ucioption.h"

#ifdef GPSFISH
#include "movegen.h"
#include "osl/misc/carray.h"
#include "osl/eval/ml/openMidEndingEval.h"
#include "osl/rating/featureSet.h"
#include "osl/progress/ml/newProgress.h"
#include "osl/enter_king/enterKing.h"
#include <vector>
#endif

using namespace std;

namespace {

  // FEN string for the initial position
#ifdef GPSFISH
  const char* StarFEN = "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1";
#else
  const char* StarFEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
#endif

  // Keep track of position keys along the setup moves (from start position to the
  // position just before to start searching). This is needed by draw detection
  // where, due to 50 moves rule, we need to check at most 100 plies back.
  StateInfo StateRingBuf[102], *SetupState = StateRingBuf;

  void set_option(istringstream& up);
  void set_position(Position& pos, istringstream& up);
  void go(Position& pos, istringstream& up);
  void perft(Position& pos, istringstream& up);
}
#ifdef GPSFISH
std::vector<Move> ignore_moves;
#endif

#ifdef GPSFISH
#define NEWGAME_TOKEN 	"usinewgame"
#define FEN_TOKEN 	"sfen"
#else
#define NEWGAME_TOKEN 	"ucinewgame"
#define FEN_TOKEN 	"fen"
#endif

/// Wait for a command from the user, parse this text string as an UCI command,
/// and calls the appropriate functions. Also intercepts EOF from stdin to
/// ensure that we exit gracefully if the GUI dies unexpectedly. In addition to
/// the UCI commands, the function also supports a few debug commands.

void uci_loop() {

  Position pos(StarFEN, false, 0); // The root position
  string cmd, token;
  bool quit = false;

  while (!quit && getline(cin, cmd))
  {
      istringstream is(cmd);

      is >> skipws >> token;

#ifdef GPSFISH
      if (cmd.size() >= 5 && string(cmd,0,5) == "echo ")
          cout << string(cmd,5) << endl;
      else
      if (cmd == "quit" || cmd == "stop" || cmd.find("gameover")==0)
#else
      if (cmd == "quit" || cmd == "stop")
#endif
      {
          quit = (token == "quit");
          Search::Signals.stop = true;
          Threads[0].wake_up(); // In case is waiting for stop or ponderhit
      }

      else if (cmd == "ponderhit")
      {
          // The opponent has played the expected move. GUI sends "ponderhit" if
          // we were told to ponder on the same move the opponent has played. We
          // should continue searching but switching from pondering to normal search.
          Search::Limits.ponder = false; // FIXME racing

          if (Search::Signals.stopOnPonderhit)
          {
              Search::Signals.stop = true;
              Threads[0].wake_up(); // In case is waiting for stop or ponderhit
          }
      }

      else if (token == "go")
          go(pos, is);

      else if (token == NEWGAME_TOKEN)
          pos.from_fen(StarFEN, false);

      else if (token == "isready")
      {
#ifdef GPSFISH
          bool ok = osl::eval::ml::OpenMidEndingEval::setUp();
          ok &= osl::progress::ml::NewProgress::setUp();
          if (! ok) {
              std::cerr << "set up failed\n";
              return;
          }
#endif
          cout << "readyok" << endl;
      }

      else if (token == "position")
          set_position(pos, is);

      else if (token == "setoption")
          set_option(is);

      else if (token == "perft")
          perft(pos, is);

      else if (token == "d")
          pos.print();

#ifndef GPSFISH
      else if (token == "flip")
          pos.flip_me();

      else if (token == "eval")
      {
          read_evaluation_uci_options(pos.side_to_move());
          cout << trace_evaluate(pos) << endl;
      }
#endif

      else if (token == "key")
#ifdef GPSFISH
          cout << "key: " << hex     << pos.get_key() << endl;
#else
          cout << "key: " << hex     << pos.get_key()
               << "\nmaterial key: " << pos.get_material_key()
               << "\npawn key: "     << pos.get_pawn_key() << endl;
#endif

#ifdef GPSFISH
      else if ( token == "ignore_moves"){
          ignore_moves.clear();
          while(is >> token) ignore_moves.push_back(move_from_uci(pos, token));
      }
#endif

#ifdef GPSFISH
      else if (token == "usi")
#else
      else if (token == "uci")
#endif
          cout << "id name "     << engine_name()
               << "\nid author " << engine_authors()
#ifdef GPSFISH
               << Options.print_all()
               << "\nusiok"      << endl;
#else
               << "\n"           << Options.print_all()
               << "\nuciok"      << endl;
#endif

#ifdef GPSFISH
      else if (token == "stop"){
      }
      else if (token == "echo"){
          is >> token;
          cout << token << endl;
      }
      else if (token == "show_tree"){
          show_tree(pos);
      }
#endif

      else
          cout << "Unknown command: " << cmd << endl;
  }
}


namespace {

  // set_position() is called when engine receives the "position" UCI
  // command. The function sets up the position described in the given
  // fen string ("fen") or the starting position ("startpos") and then
  // makes the moves given in the following move list ("moves").

  void set_position(Position& pos, istringstream& is) {

    Move m;
    string token, fen;

#ifdef GPSFISH
    ignore_moves.clear();
#endif
    is >> token;

    if (token == "startpos")
    {
        fen = StarFEN;
        is >> token; // Consume "moves" token if any
    }
    else if (token == FEN_TOKEN)
        while (is >> token && token != "moves")
            fen += token + " ";
    else
        return;

#ifdef GPSFISH
    pos.from_fen(fen, false);
#else
    pos.from_fen(fen, Options["UCI_Chess960"].value<bool>());
#endif

    // Parse move list (if any)
    while (is >> token && (m = move_from_uci(pos, token)) != MOVE_NONE)
    {
        pos.do_move(m, *SetupState);

        // Increment pointer to StateRingBuf circular buffer
        if (++SetupState - StateRingBuf >= 102)
            SetupState = StateRingBuf;
    }

#ifdef GPSFISH
    assert(pos.eval_is_ok());
#endif
  }


  // set_option() is called when engine receives the "setoption" UCI
  // command. The function updates the corresponding UCI option ("name")
  // to the given value ("value").

  void set_option(istringstream& is) {

    string token, name, value;

    is >> token; // Consume "name" token

    // Read option name (can contain spaces)
    while (is >> token && token != "value")
        name += string(" ", !name.empty()) + token;

    // Read option value (can contain spaces)
    while (is >> token)
        value += string(" ", !value.empty()) + token;

    if (Options.find(name) != Options.end())
        Options[name].set_value(value.empty() ? "true" : value); // UCI buttons don't have "value"
    else
        cout << "No such option: " << name << endl;
  }


  // go() is called when engine receives the "go" UCI command. The
  // function sets the thinking time and other parameters from the input
  // string, and then calls think(). Returns false if a quit command
  // is received while thinking, true otherwise.

  void go(Position& pos, istringstream& is) {

    string token;
#ifdef GPSFISH
    osl::CArray<int,2> time={{0,0}},inc={{0,0}};
#else
    int time[] = { 0, 0 }, inc[] = { 0, 0 };
#endif

    memset(&Search::Limits, 0, sizeof(Search::Limits));
    Search::RootMoves.clear();
    Search::RootPosition = &pos;

    while (is >> token)
    {
        if (token == "infinite")
            Search::Limits.infinite = true;
        else if (token == "ponder")
            Search::Limits.ponder = true;
        else if (token == "wtime")
            is >> time[WHITE];
        else if (token == "btime")
            is >> time[BLACK];
        else if (token == "winc")
            is >> inc[WHITE];
        else if (token == "binc")
            is >> inc[BLACK];
        else if (token == "movestogo")
            is >> Search::Limits.movesToGo;
        else if (token == "depth")
            is >> Search::Limits.maxDepth;
        else if (token == "nodes")
            is >> Search::Limits.maxNodes;
#ifdef GPSFISH
        else if (token == "mate"){
            int mateTime;
            is >> mateTime;
            do_checkmate(pos, mateTime);
            return;
        }
        else if (token == "movetime" || token=="byoyomi")
#else
        else if (token == "movetime")
#endif
            is >> Search::Limits.maxTime;
        else if (token == "searchmoves")
            while (is >> token)
                Search::RootMoves.push_back(move_from_uci(pos, token));
    }

    Search::RootMoves.push_back(MOVE_NONE);
    Search::Limits.time = time[pos.side_to_move()];
    Search::Limits.increment = inc[pos.side_to_move()];

#if 0 //def GPSFISH
    if(searchMoves == cur && !ignore_moves.empty()){
        MoveStack mlist[MAX_MOVES];
        MoveStack* last = pos.in_check() ? generate<MV_EVASION>(pos, mlist)
                                         : generate<MV_NON_EVASION>(pos, mlist);

        for(MoveStack* mp=mlist;mp<last;mp++){
            if(find(ignore_moves.begin(),ignore_moves.end(),mp->move)==ignore_moves.end()){
                *cur++= mp->move;
            }
        }
        *cur = MOVE_NONE;
    }
    ignore_moves.clear();
    if(!using_tcp_connection
            && osl::EnterKing::canDeclareWin(pos.osl_state)){
        cout << "bestmove win" << endl;
        return true;
    }
#endif

    Threads.start_thinking();
  }


  // perft() is called when engine receives the "perft" command.
  // The function calls perft() passing the required search depth
  // then prints counted leaf nodes and elapsed time.

  void perft(Position& pos, istringstream& is) {

    int depth, time;
    int64_t n;

    if (!(is >> depth))
        return;

    time = get_system_time();

    n = Search::perft(pos, depth * ONE_PLY);

    time = get_system_time() - time;

    std::cout << "\nNodes " << n
              << "\nTime (ms) " << time
              << "\nNodes/second " << int(n / (time / 1000.0)) << std::endl;
  }
}
