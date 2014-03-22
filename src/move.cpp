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
#include <cstring>
#include <string>

#include "move.h"
#include "movegen.h"
#include "position.h"
#ifdef GPSFISH
#include "osl/record/usi.h"
#include "osl/record/csa.h"
#endif

using std::string;

#ifdef GPSFISH
bool using_tcp_connection = false;
#endif

/// move_to_uci() converts a move to a string in coordinate notation
/// (g1f3, a7a8q, etc.). The only special case is castling moves, where we
/// print in the e1g1 notation in normal chess mode, and in e1h1 notation in
/// Chess960 mode. Instead internally Move is coded as "king captures rook".

const string move_to_uci(Move m, bool chess960) {

#ifdef GPSFISH
  return osl::record::usi::show(m);
#else
  Square from = move_from(m);
  Square to = move_to(m);
  string promotion;

  if (m == MOVE_NONE)
      return "(none)";

  if (m == MOVE_NULL)
      return "0000";

  if (move_is_castle(m) && !chess960)
      to = from + (square_file(to) == FILE_H ? Square(2) : -Square(2));

  if (move_is_promotion(m))
      promotion = char(tolower(piece_type_to_char(promotion_piece_type(m))));

  return square_to_string(from) + square_to_string(to) + promotion;
#endif
}


/// move_from_uci() takes a position and a string representing a move in
/// simple coordinate notation and returns an equivalent Move if any.
/// Moves are guaranteed to be legal.

Move move_from_uci(const Position& pos, const string& str) {

#ifdef GPSFISH
  return osl::record::usi::strToMove(str,pos.osl_state);
#else
  for (MoveList<MV_LEGAL> ml(pos); !ml.end(); ++ml)
      if (str == move_to_uci(ml.move(), pos.is_chess960()))
          return ml.move();

  return MOVE_NONE;
#endif
}


/// move_to_san() takes a position and a move as input, where it is assumed
/// that the move is a legal move for the position. The return value is
/// a string containing the move in short algebraic notation.

#ifdef GPSFISH
const string move_to_san(Position&, Move m) {
  return osl::record::csa::show(m);
}
#else
const string move_to_san(Position& pos, Move m) {

  if (m == MOVE_NONE)
      return "(none)";

  if (m == MOVE_NULL)
      return "(null)";

  assert(move_is_ok(m));

  Bitboard attackers;
  bool ambiguousMove, ambiguousFile, ambiguousRank;
  Square sq, from = move_from(m);
  Square to = move_to(m);
  PieceType pt = piece_type(pos.piece_on(from));
  string san;

  if (move_is_castle(m))
      san = (move_to(m) < move_from(m) ? "O-O-O" : "O-O");
  else
  {
      if (pt != PAWN)
      {
          san = piece_type_to_char(pt);

          // Disambiguation if we have more then one piece with destination 'to'
          // note that for pawns is not needed because starting file is explicit.
          attackers = pos.attackers_to(to) & pos.pieces(pt, pos.side_to_move());
          clear_bit(&attackers, from);
          ambiguousMove = ambiguousFile = ambiguousRank = false;

          while (attackers)
          {
              sq = pop_1st_bit(&attackers);

              if (square_file(sq) == square_file(from))
                  ambiguousFile = true;

              if (square_rank(sq) == square_rank(from))
                  ambiguousRank = true;

              ambiguousMove = true;
          }

          if (ambiguousMove)
          {
              if (!ambiguousFile)
                  san += file_to_char(square_file(from));
              else if (!ambiguousRank)
                  san += rank_to_char(square_rank(from));
              else
                  san += square_to_string(from);
          }
      }

      if (pos.move_is_capture(m))
      {
          if (pt == PAWN)
              san += file_to_char(square_file(from));

          san += 'x';
      }

      san += square_to_string(to);

      if (move_is_promotion(m))
      {
          san += '=';
          san += piece_type_to_char(promotion_piece_type(m));
      }
  }

  // The move gives check? We don't use pos.move_gives_check() here
  // because we need to test for a mate after the move is done.
  StateInfo st;
  pos.do_move(m, st);
  if (pos.in_check())
      san += pos.is_mate() ? "#" : "+";
  pos.undo_move(m);

  return san;
}
#endif



