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

#include <fstream>
#include <iostream>
#include <istream>
#include <vector>

#include "misc.h"
#include "position.h"
#include "search.h"
#include "thread.h"
#include "tt.h"
#include "ucioption.h"
#include "misc.h"

using namespace std;

static const char* Defaults[] = {
#ifdef GPSFISH
"kng4nl/lsg2r3/pppppsbpp/5pp2/7P1/2P1P1PS1/PP1PSP2P/1BK1G2R1/LN1G3NL w - 1",
"l6nl/1r3sgk1/2np1gspp/2pbppp2/pp1P4P/2P1P1PP1/PPSG1P2L/1KGB1S2R/LN5N1 w - 1",
"kng1g2nl/ls7/pppps1bpp/4p1p2/7P1/2PS1rP1P/PPBP5/L1G2G1R1/KNS4NL w 2Pp 1",
"ln2gk2l/3s2gs1/2ppppn1p/pr7/9/P1P3R2/3PPPP1P/1SG1KSG2/LN5NL b B3Pb2p 1",

"lns2g1n1/1r3ks2/p1pp1p1pp/3gp1p2/9/2P1L3P/P1+BP1PPP1/1S2RK3/LN1G1GSNL b Pb2p 1",
"ln3gsnl/1r1s3k1/p2pp1bpp/5pp2/4R4/PB1P5/1P2PPPPP/5KS2/LN1G1G1NL w G3Ps 1",
"ln4p2/2gkgs1+R1/ppsppp3/8p/9/1P7/P1PPb1PPP/1SG1R4/LN5KL w B2NLPgs3p 1",
"l4k1nl/3b2g2/p5spp/2pp2p2/4P4/2rP2P2/PP2RP1PP/2GS5/LNBK3NL b 2S2P2gn2p 1",

"ln1g1B2l/1sk1g2s1/ppp1ppnpp/3p2r2/3N5/2RKBP3/PP1PPGgPP/1S7/L6sL w NP2p 1",
"ln4R1l/2k2g3/pppp2n1p/9/P3Spp2/2P6/1P1PP1P1P/1KG1+s1+p2/LN5NL w 2B2Pr2g2sp 1",
"4r4/1kg2+L2l/1s1g5/ppp4pp/4ppp2/LPPS4P/P3PP3/g1K6/1N4R1L w B2S3Nbg4p 1",
"7nk/6ssl/7pp/p1p2p3/1p6P/P1P3pL1/1P3PNP1/6P1L/3+RP1N1K w RB2GNLb2g2s3p 1",

"1n1g4l/1ks1g4/ppppps1p1/5p3/4P3P/2PB1G2L/1P1P1P1P1/6+r2/1N2K4 b BGSN2L3Prsnp 1",
"4k4/1sG1g4/lpPpp1+L2/2p1s3N/3P4r/1R5pp/3bPGPP1/6K2/6SNL b B2NL4Pgs3p 1",
"ln6+B/1Sk5l/2ps5/pg2g2pp/1NNp3N1/PK2PP+b1P/4S4/7R1/L7L w RGS7Pg2p 1",
"3g3+B1/1Rs2+P3/3kp2p1/Nppp2p1p/pn2L2N1/2P5P/LP1PP4/PG1+r5/KG7 b SLPbg2snl2p 1"
#else
  "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
  "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 10",
  "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 11",
  "4rrk1/pp1n3p/3q2pQ/2p1pb2/2PP4/2P3N1/P2B2PP/4RRK1 b - - 7 19",
  "rq3rk1/ppp2ppp/1bnpb3/3N2B1/3NP3/7P/PPPQ1PP1/2KR3R w - - 7 14",
  "r1bq1r1k/1pp1n1pp/1p1p4/4p2Q/4Pp2/1BNP4/PPP2PPP/3R1RK1 w - - 2 14",
  "r3r1k1/2p2ppp/p1p1bn2/8/1q2P3/2NPQN2/PPP3PP/R4RK1 b - - 2 15",
  "r1bbk1nr/pp3p1p/2n5/1N4p1/2Np1B2/8/PPP2PPP/2KR1B1R w kq - 0 13",
  "r1bq1rk1/ppp1nppp/4n3/3p3Q/3P4/1BP1B3/PP1N2PP/R4RK1 w - - 1 16",
  "4r1k1/r1q2ppp/ppp2n2/4P3/5Rb1/1N1BQ3/PPP3PP/R5K1 w - - 1 17",
  "2rqkb1r/ppp2p2/2npb1p1/1N1Nn2p/2P1PP2/8/PP2B1PP/R1BQK2R b KQ - 0 11",
  "r1bq1r1k/b1p1npp1/p2p3p/1p6/3PP3/1B2NN2/PP3PPP/R2Q1RK1 w - - 1 16",
  "3r1rk1/p5pp/bpp1pp2/8/q1PP1P2/b3P3/P2NQRPP/1R2B1K1 b - - 6 22",
  "r1q2rk1/2p1bppp/2Pp4/p6b/Q1PNp3/4B3/PP1R1PPP/2K4R w - - 2 18",
  "4k2r/1pb2ppp/1p2p3/1R1p4/3P4/2r1PN2/P4PPP/1R4K1 b - - 3 22",
  "3q2k1/pb3p1p/4pbp1/2r5/PpN2N2/1P2P2P/5PP1/Q2R2K1 b - - 4 26",
  "6k1/6p1/6Pp/ppp5/3pn2P/1P3K2/1PP2P2/3N4 b - - 0 1",
  "3b4/5kp1/1p1p1p1p/pP1PpP1P/P1P1P3/3KN3/8/8 w - - 0 1",
  "2K5/p7/7P/5pR1/8/5k2/r7/8 w - - 0 1",
  "8/6pk/1p6/8/PP3p1p/5P2/4KP1q/3Q4 w - - 0 1",
  "7k/3p2pp/4q3/8/4Q3/5Kp1/P6b/8 w - - 0 1",
  "8/2p5/8/2kPKp1p/2p4P/2P5/3P4/8 w - - 0 1",
  "8/1p3pp1/7p/5P1P/2k3P1/8/2K2P2/8 w - - 0 1",
  "8/pp2r1k1/2p1p3/3pP2p/1P1P1P1P/P5KR/8/8 w - - 0 1",
  "8/3p4/p1bk3p/Pp6/1Kp1PpPp/2P2P1P/2P5/5B2 b - - 0 1",
  "5k2/7R/4P2p/5K2/p1r2P1p/8/8/8 b - - 0 1",
  "6k1/6p1/P6p/r1N5/5p2/7P/1b3PP1/4R1K1 w - - 0 1",
  "1r3k2/4q3/2Pp3b/3Bp3/2Q2p2/1p1P2P1/1P2KP2/3N4 w - - 0 1",
  "6k1/4pp1p/3p2p1/P1pPb3/R7/1r2P1PP/3B1P2/6K1 w - - 0 1",
  "8/3p3B/5p2/5P2/p7/PP5b/k7/6K1 w - - 0 1"
#endif
};


/// benchmark() runs a simple benchmark by letting Stockfish analyze a set
/// of positions for a given limit each. There are five parameters; the
/// transposition table size, the number of search threads that should
/// be used, the limit value spent for each position (optional, default is
/// depth 12), an optional file name where to look for positions in fen
/// format (defaults are the positions defined above) and the type of the
/// limit value: depth (default), time in secs or number of nodes.

void benchmark(const Position& current, istream& is) {

#ifdef GPSFISH
  bool ok = osl::eval::ml::OpenMidEndingEval::setUp();
  ok &= osl::progress::ml::NewProgress::setUp();
  if (! ok) {
    std::cerr << "set up failed\n";
    return;
  }
#endif

  string token;
  Search::LimitsType limits;
  vector<string> fens;

  // Assign default values to missing arguments
  string ttSize    = (is >> token) ? token : "32";
  string threads   = (is >> token) ? token : "1";
  string limit     = (is >> token) ? token : "13";
  string fenFile   = (is >> token) ? token : "default";
  string limitType = (is >> token) ? token : "depth";

  Options["Hash"]    = ttSize;
  Options["Threads"] = threads;
  TT.clear();

  if (limitType == "time")
      limits.movetime = 1000 * atoi(limit.c_str()); // movetime is in ms

  else if (limitType == "nodes")
      limits.nodes = atoi(limit.c_str());

  else if (limitType == "mate")
      limits.mate = atoi(limit.c_str());

  else
      limits.depth = atoi(limit.c_str());

  if (fenFile == "default")
      fens.assign(Defaults, Defaults + 30);

  else if (fenFile == "current")
      fens.push_back(current.fen());

  else
  {
      string fen;
      ifstream file(fenFile.c_str());

      if (!file.is_open())
      {
          cerr << "Unable to open file " << fenFile << endl;
          return;
      }

      while (getline(file, fen))
          if (!fen.empty())
              fens.push_back(fen);

      file.close();
  }

  int64_t nodes = 0;
  Search::StateStackPtr st;
  Time::point elapsed = Time::now();

  for (size_t i = 0; i < fens.size(); ++i)
  {
      Position pos(fens[i], Options["UCI_Chess960"], Threads.main());

      cerr << "\nPosition: " << i + 1 << '/' << fens.size() << endl;

      if (limitType == "perft")
      {
          size_t cnt = Search::perft(pos, limits.depth * ONE_PLY);
          cerr << "\nPerft " << limits.depth  << " leaf nodes: " << cnt << endl;
          nodes += cnt;
      }
      else
      {
          Threads.start_thinking(pos, limits, vector<Move>(), st);
          Threads.wait_for_think_finished();
          nodes += Search::RootPos.nodes_searched();
      }
  }

  elapsed = Time::now() - elapsed + 1; // Assure positive to avoid a 'divide by zero'

  cerr << "\n==========================="
       << "\nTotal time (ms) : " << elapsed
       << "\nNodes searched  : " << nodes
       << "\nNodes/second    : " << 1000 * nodes / elapsed << endl;
}
