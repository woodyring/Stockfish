/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2013 Marco Costalba, Joona Kiiski, Tord Romstad

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

#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>

#include "evaluate.h"
#include "notation.h"
#include "position.h"
#include "search.h"
#include "thread.h"
#include "ucioption.h"

#ifdef GPSFISH
#include "tt.h"
#include "movegen.h"
#include "osl/eval/openMidEndingEval.h"
#include "osl/progress.h"
#include "osl/enterKing.h"
#include <vector>
#endif

using namespace std;

extern void benchmark(const Position& pos, istream& is);

namespace {

  // FEN string of the initial position, normal chess
#ifdef GPSFISH
  const char* StartFEN = "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1";
#else
  const char* StartFEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
#endif

  // Keep track of position keys along the setup moves (from start position to the
  // position just before to start searching). Needed by repetition draw detection.
  Search::StateStackPtr SetupStates;

  void setoption(istringstream& up);
  void position(Position& pos, istringstream& up);
  void go(const Position& pos, istringstream& up);
}
#ifdef GPSFISH
std::vector<Move> ignore_moves;
#endif

/// Wait for a command from the user, parse this text string as an UCI command,
/// and call the appropriate functions. Also intercepts EOF from stdin to ensure
/// that we exit gracefully if the GUI dies unexpectedly. In addition to the UCI
/// commands, the function also supports a few debug commands.

void UCI::loop(const string& args) {

  Position pos(StartFEN, false, Threads.main()); // The root position
  string token, cmd = args;

  do {
      if (args.empty() && !getline(cin, cmd)) // Block here waiting for input
          cmd = "quit";

      istringstream is(cmd);

      is >> skipws >> token;

#ifdef GPSFISH
      if (token.size() >= 5 && string(token,0,5) == "echo ")
          cout << string(token,5) << endl;
      else
      if (token == "quit" || token == "stop" || token == "ponderhit" || token.find("gameover")==0)
#else
      if (token == "quit" || token == "stop" || token == "ponderhit")
#endif
      {
          // GUI sends 'ponderhit' to tell us to ponder on the same move the
          // opponent has played. In case Signals.stopOnPonderhit is set we are
          // waiting for 'ponderhit' to stop the search (for instance because we
          // already ran out of time), otherwise we should continue searching but
          // switching from pondering to normal search.
          if (token != "ponderhit" || Search::Signals.stopOnPonderhit)
          {
              Search::Signals.stop = true;
              Threads.main()->notify_one(); // Could be sleeping
          }
          else
              Search::Limits.ponder = false;
      }
      else if (token == "perft" && (is >> token)) // Read perft depth
      {
          stringstream ss;

          ss << Options["Hash"]    << " "
             << Options["Threads"] << " " << token << " current perft";

          benchmark(pos, ss);
      }

#ifdef GPSFISH
      else if (token == "key")
          sync_cout <<   "position key: " << hex << pos.key() << sync_endl;
#else
      else if (token == "key")
          sync_cout << hex << uppercase << setfill('0')
                    << "position key: "   << setw(16) << pos.key()
                    << "\nmaterial key: " << setw(16) << pos.material_key()
                    << "\npawn key:     " << setw(16) << pos.pawn_key()
                    << dec << sync_endl;

#endif
#ifdef GPSFISH
      else if (token == "usi")
          sync_cout << "id name " << engine_info(true)
                    << Options
                    << "\nusiok"  << sync_endl;
#else
      else if (token == "uci")
          sync_cout << "id name " << engine_info(true)
                    << "\n"       << Options
                    << "\nuciok"  << sync_endl;
#endif

#ifdef GPSFISH
      else if (token == "usinewgame") {  pos.set(StartFEN, false, Threads.main()); TT.clear(); }
#else
      else if (token == "eval")
      {
          Search::RootColor = pos.side_to_move(); // Ensure it is set
          sync_cout << Eval::trace(pos) << sync_endl;
      }
      else if (token == "ucinewgame") { /* Avoid returning "Unknown command" */ }
#endif
      else if (token == "go")         go(pos, is);
      else if (token == "position")   position(pos, is);
      else if (token == "setoption")  setoption(is);
#ifndef GPSFISH
      else if (token == "flip")       pos.flip();
#endif
      else if (token == "bench")      benchmark(pos, is);
      else if (token == "d")          sync_cout << pos.pretty() << sync_endl;
#ifdef GPSFISH
      else if (token == "isready") {
          bool ok = osl::eval::ml::OpenMidEndingEval::setUp();
          ok &= osl::progress::ml::NewProgress::setUp();
          if (! ok) {
              std::cerr << "set up failed\n";
              return;
          }
          sync_cout << "readyok" << sync_endl;
      }
      else if ( token == "ignore_moves"){
          ignore_moves.clear();
          while(is >> token) ignore_moves.push_back(move_from_uci(pos, token));
      }
      else if (token == "stop"){
      }
      else if (token == "echo"){
          is >> token;
          cout << token << endl;
      }
      else if (token == "show_tree"){
          show_tree(pos);
      }
#else
      else if (token == "isready")    sync_cout << "readyok" << sync_endl;
#endif
      else
          sync_cout << "Unknown command: " << cmd << sync_endl;

  } while (token != "quit" && args.empty()); // Args have one-shot behaviour

  Threads.wait_for_think_finished(); // Cannot quit while search is running
}


namespace {

  // position() is called when engine receives the "position" UCI command.
  // The function sets up the position described in the given fen string ("fen")
  // or the starting position ("startpos") and then makes the moves given in the
  // following move list ("moves").

  void position(Position& pos, istringstream& is) {

    Move m;
    string token, fen;

#ifdef GPSFISH
    ignore_moves.clear();
#endif
    is >> token;

    if (token == "startpos")
    {
        fen = StartFEN;
        is >> token; // Consume "moves" token if any
    }
#ifdef GPSFISH
    else if (token == "sfen")
#else
    else if (token == "fen")
#endif
        while (is >> token && token != "moves")
            fen += token + " ";
    else
        return;

#ifdef GPSFISH
    pos.set(fen, false, Threads.main());
#else
    pos.set(fen, Options["UCI_Chess960"], Threads.main());
#endif

    SetupStates = Search::StateStackPtr(new std::stack<StateInfo>());

    // Parse move list (if any)
    while (is >> token && (m = move_from_uci(pos, token)) != MOVE_NONE)
    {
        SetupStates->push(StateInfo());
        pos.do_move(m, SetupStates->top());
    }

#ifdef GPSFISH
    assert(pos.eval_is_ok());
#endif
  }


  // setoption() is called when engine receives the "setoption" UCI command. The
  // function updates the UCI option ("name") to the given value ("value").

  void setoption(istringstream& is) {

    string token, name, value;

    is >> token; // Consume "name" token

    // Read option name (can contain spaces)
    while (is >> token && token != "value")
        name += string(" ", !name.empty()) + token;

#ifdef GPSFISH
    // shogidokoro hack
    if( ( strncmp("UCI_",name.c_str(),4) != 0 ) &&
        ( strncmp("USI_",name.c_str(),4) != 0 ) ) {
        std::string newName = UCI::strReplace( name, "_", " " );
        name = newName;
    }
#endif

    // Read option value (can contain spaces)
    while (is >> token)
        value += string(" ", !value.empty()) + token;

    if (Options.count(name))
        Options[name] = value;
    else
        sync_cout << "No such option: " << name << sync_endl;
  }


  // go() is called when engine receives the "go" UCI command. The function sets
  // the thinking time and other parameters from the input string, and starts
  // the search.

  void go(const Position& pos, istringstream& is) {

    Search::LimitsType limits;
    vector<Move> searchMoves;

    string token;

    while (is >> token)
    {
        if (token == "searchmoves")
            while (is >> token)
                searchMoves.push_back(move_from_uci(pos, token));

        else if (token == "wtime")     is >> limits.time[WHITE];
        else if (token == "btime")     is >> limits.time[BLACK];
        else if (token == "winc")      is >> limits.inc[WHITE];
        else if (token == "binc")      is >> limits.inc[BLACK];
        else if (token == "movestogo") is >> limits.movestogo;
        else if (token == "depth")     is >> limits.depth;
        else if (token == "nodes")     is >> limits.nodes;
#ifdef GPSFISH
        else if (token == "mate"){
            int mateTime;
            is >> mateTime;
            do_checkmate(pos, mateTime);
            return;
        }
        else if (token == "movetime" || token=="byoyomi") is >> limits.movetime;
#else
        else if (token == "movetime")  is >> limits.movetime;
#endif
        else if (token == "mate")      is >> limits.mate;
        else if (token == "infinite")  limits.infinite = true;
        else if (token == "ponder")    limits.ponder = true;
    }

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

    Threads.start_thinking(pos, limits, searchMoves, SetupStates);
  }
}
