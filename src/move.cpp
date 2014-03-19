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
#include <iomanip>
#include <string>
#include <sstream>

#include "move.h"
#include "movegen.h"
#include "search.h"
#ifdef GPSFISH
#include "osl/record/usi.h"
#include "osl/record/csa.h"
#endif

using std::string;

namespace {
  const string time_string(int milliseconds);
  const string score_string(Value v);
}

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


/// pretty_pv() creates a human-readable string from a position and a PV.
/// It is used to write search information to the log file (which is created
/// when the UCI parameter "Use Search Log" is "true").

const string pretty_pv(Position& pos, int depth, Value score, int time, Move pv[]) {

  const int64_t K = 1000;
  const int64_t M = 1000000;
  const int startColumn = 28;
  const size_t maxLength = 80 - startColumn;
  const string lf = string("\n") + string(startColumn, ' ');

  StateInfo state[PLY_MAX_PLUS_2], *st = state;
  Move* m = pv;
  string san;
  std::stringstream s;
  size_t length = 0;

  // First print depth, score, time and searched nodes...
  s << std::setw(2) << depth
    << std::setw(8) << score_string(score)
    << std::setw(8) << time_string(time);

  if (pos.nodes_searched() < M)
      s << std::setw(8) << pos.nodes_searched() / 1 << "  ";
  else if (pos.nodes_searched() < K * M)
      s << std::setw(7) << pos.nodes_searched() / K << "K  ";
  else
      s << std::setw(7) << pos.nodes_searched() / M << "M  ";

#ifdef GPSFISH
  Position pos_backup(pos,pos.thread());
#endif
  // ...then print the full PV line in short algebraic notation
  while (*m != MOVE_NONE)
  {
#ifdef GPSFISH
      san = move_to_san(pos_backup, *m);
#else
      san = move_to_san(pos, *m);
#endif
      length += san.length() + 1;

      if (length > maxLength)
      {
          length = san.length() + 1;
          s << lf;
      }
      s << san << ' ';

#ifdef GPSFISH
      pos_backup.do_move(*m++, *st++);
#else
      pos.do_move(*m++, *st++);
#endif
  }

  // Restore original position before to leave
#ifndef GPSFISH
  while (m != pv) pos.undo_move(*--m);
#endif

  return s.str();
}


namespace {

  const string time_string(int millisecs) {

    const int MSecMinute = 1000 * 60;
    const int MSecHour   = 1000 * 60 * 60;

    int hours = millisecs / MSecHour;
    int minutes =  (millisecs % MSecHour) / MSecMinute;
    int seconds = ((millisecs % MSecHour) % MSecMinute) / 1000;

    std::stringstream s;

    if (hours)
        s << hours << ':';

    s << std::setfill('0') << std::setw(2) << minutes << ':' << std::setw(2) << seconds;
    return s.str();
  }


  const string score_string(Value v) {

    std::stringstream s;

    if (v >= VALUE_MATE - 200)
        s << "#" << (VALUE_MATE - v + 1) / 2;
    else if (v <= -VALUE_MATE + 200)
        s << "-#" << (VALUE_MATE + v) / 2;
    else
        s << std::setprecision(2) << std::fixed << std::showpos << float(v) / PawnValueMidgame;

    return s.str();
  }
}
