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

#if !defined MOVEPICK_H_INCLUDED
#define MOVEPICK_H_INCLUDED

#include <algorithm> // For std::max
#include <cstring>   // For memset

#include "movegen.h"
#include "position.h"
#include "search.h"
#include "types.h"


/// The Stats struct stores moves statistics. According to the template parameter
/// the class can store both History and Gains type statistics. History records
/// how often different moves have been successful or unsuccessful during the
/// current search and is used for reduction and move ordering decisions. Gains
/// records the move's best evaluation gain from one ply to the next and is used
/// for pruning decisions. Entries are stored according only to moving piece and
/// destination square, in particular two moves with different origin but same
/// destination and same piece will be considered identical.
template<bool Gain>
struct Stats {

  static const Value Max = Value(2000);

#ifdef GPSFISH
  const Value* operator[](Piece p) const { return &table[ptypeOIndex(p)][0]; }
#else
  const Value* operator[](Piece p) const { return &table[p][0]; }
#endif
  void clear() { memset(table, 0, sizeof(table)); }

#ifdef GPSFISH
  void update(Piece p_, Square to_, Value v) {
      int p  = ptypeOIndex(p_);
      int to = to_.index();
#else
  void update(Piece p, Square to, Value v) {
#endif

    if (Gain)
        table[p][to] = std::max(v, table[p][to] - 1);

    else if (abs(table[p][to] + v) < Max)
        table[p][to] +=  v;
  }

private:
  Value table[PIECE_NB][SQUARE_NB];
};

typedef Stats<false> History;
typedef Stats<true> Gains;


/// MovePicker class is used to pick one pseudo legal move at a time from the
/// current position. The most important method is next_move(), which returns a
/// new pseudo legal move each time it is called, until there are no moves left,
/// when MOVE_NONE is returned. In order to improve the efficiency of the alpha
/// beta algorithm, MovePicker attempts to return the moves which are most likely
/// to get a cut-off first.

class MovePicker {

  MovePicker& operator=(const MovePicker&); // Silence a warning under MSVC

public:
  MovePicker(const Position&, Move, Depth, const History&, Search::Stack*, Value);
  MovePicker(const Position&, Move, Depth, const History&, Square);
  MovePicker(const Position&, Move, const History&, PieceType);
  template<bool SpNode> Move next_move();

private:
  template<GenType> void score();
  void generate_next();

  const Position& pos;
  const History& Hist;
  Search::Stack* ss;
  Depth depth;
  Move ttMove;
  MoveStack killers[2];
  Square recaptureSquare;
  int captureThreshold, phase;
  MoveStack *cur, *end, *endQuiets, *endBadCaptures;
  MoveStack moves[MAX_MOVES];
};

#endif // !defined(MOVEPICK_H_INCLUDED)
