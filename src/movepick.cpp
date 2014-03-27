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

#include "movegen.h"
#include "movepick.h"

namespace {

  enum Sequencer {
    MAIN_SEARCH,         TT_MOVE_S1, CAPTURES_S1, KILLERS_S1, QUIETS_1_S1,
                         QUIETS_2_S1, BAD_CAPTURES_S1, STOP_S1,
    EVASIONS,            TT_MOVE_S2, EVASIONS_S2, STOP_S2,
    CAPTURES_AND_CHECKS, TT_MOVE_S3, CAPTURES_S3, QUIET_CHECKS_S3, STOP_S3,
    CAPTURES,            TT_MOVE_S4, CAPTURES_S4, STOP_S4,
    PROBCUT,             TT_MOVE_S5, CAPTURES_S5, STOP_S5,
    RECAPTURES,          CAPTURES_S6, STOP_S6
  };

  // Unary predicate used by std::partition to split positive scores from remaining
  // ones so to sort separately the two sets, and with the second sort delayed.
  inline bool has_positive_score(const MoveStack& move) { return move.score > 0; }

  // Picks and moves to the front the best move in the range [firstMove, lastMove),
  // it is faster than sorting all the moves in advance when moves are few, as
  // normally are the possible captures.
  inline MoveStack* pick_best(MoveStack* firstMove, MoveStack* lastMove)
  {
      std::swap(*firstMove, *std::max_element(firstMove, lastMove));
      return firstMove;
  }
}


/// Constructors of the MovePicker class. As arguments we pass information
/// to help it to return the presumably good moves first, to decide which
/// moves to return (in the quiescence search, for instance, we only want to
/// search captures, promotions and some checks) and about how important good
/// move ordering is at the current node.

MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const History& h,
                       Search::Stack* ss, Value beta) : pos(p), H(h), depth(d) {

  assert(d > DEPTH_ZERO);

  captureThreshold = 0;
  curMove = lastMove = 0;
  badCaptures = moves + MAX_MOVES;

  if (p.in_check())
      phase = EVASIONS;

  else
  {
      killers[0].move = ss->killers[0];
      killers[1].move = ss->killers[1];

      // Consider sligtly negative captures as good if at low depth and far from beta
      if (ss && ss->eval < beta - PawnValueMidgame && d < 3 * ONE_PLY)
          captureThreshold = -PawnValueMidgame;

      // Consider negative captures as good if still enough to reach beta
      else if (ss && ss->eval > beta)
          captureThreshold = beta - ss->eval;

      phase = MAIN_SEARCH;
  }

  ttMove = (ttm && pos.is_pseudo_legal(ttm) ? ttm : MOVE_NONE);
  phase += (ttMove == MOVE_NONE);
}

MovePicker::MovePicker(const Position& p, Move ttm, Depth d, const History& h,
                       Square sq) : pos(p), H(h), curMove(0), lastMove(0) {

  assert(d <= DEPTH_ZERO);

  if (p.in_check())
      phase = EVASIONS;

  else if (d >= DEPTH_QS_CHECKS)
      phase = CAPTURES_AND_CHECKS;

  else if (d >= DEPTH_QS_RECAPTURES)
  {
      phase = CAPTURES;

      // Skip TT move if is not a capture or a promotion, this avoids qsearch
      // tree explosion due to a possible perpetual check or similar rare cases
      // when TT table is full.
      if (ttm && !pos.is_capture_or_promotion(ttm))
          ttm = MOVE_NONE;
  }
  else
  {
      phase = RECAPTURES - 1;
      recaptureSquare = sq;
      ttm = MOVE_NONE;
  }

  ttMove = (ttm && pos.is_pseudo_legal(ttm) ? ttm : MOVE_NONE);
  phase += (ttMove == MOVE_NONE);
}

MovePicker::MovePicker(const Position& p, Move ttm, const History& h,
                       PieceType parentCapture) : pos(p), H(h) {

  assert (!pos.in_check());

  // In ProbCut we consider only captures better than parent's move
  captureThreshold = PieceValueMidgame[Piece(parentCapture)];
  curMove = lastMove = 0;
  phase = PROBCUT;

  if (   ttm != MOVE_NONE
      && (!pos.is_capture(ttm) ||  pos.see(ttm) <= captureThreshold))
      ttm = MOVE_NONE;

  ttMove = (ttm && pos.is_pseudo_legal(ttm) ? ttm : MOVE_NONE);
  phase += (ttMove == MOVE_NONE);
}


/// MovePicker::score_captures(), MovePicker::score_noncaptures() and
/// MovePicker::score_evasions() assign a numerical move ordering score
/// to each move in a move list.  The moves with highest scores will be
/// picked first by next_move().

void MovePicker::score_captures() {
  // Winning and equal captures in the main search are ordered by MVV/LVA.
  // Suprisingly, this appears to perform slightly better than SEE based
  // move ordering. The reason is probably that in a position with a winning
  // capture, capturing a more valuable (but sufficiently defended) piece
  // first usually doesn't hurt. The opponent will have to recapture, and
  // the hanging piece will still be hanging (except in the unusual cases
  // where it is possible to recapture with the hanging piece). Exchanging
  // big pieces before capturing a hanging piece probably helps to reduce
  // the subtree size.
  // In main search we want to push captures with negative SEE values to
  // badCaptures[] array, but instead of doing it now we delay till when
  // the move has been picked up in pick_move_from_list(), this way we save
  // some SEE calls in case we get a cutoff (idea from Pablo Vazquez).
  Move m;

  for (MoveStack* cur = moves; cur != lastMove; cur++)
  {
      m = cur->move;
      cur->score =  PieceValueMidgame[pos.piece_on(to_sq(m))]
                  - type_of(pos.piece_moved(m));

      if (is_promotion(m))
#ifdef GPSFISH
          cur->score ++; // XXX , calc correct value ?
#else
          cur->score += PieceValueMidgame[Piece(promotion_piece_type(m))];
#endif
  }
}

void MovePicker::score_noncaptures() {

  Move m;
  Square from;

  for (MoveStack* cur = moves; cur != lastMove; cur++)
  {
      m = cur->move;
#ifdef GPSFISH
      cur->score = H.value(m.ptypeO(), to_sq(m));
#else
      from = from_sq(m);
      cur->score = H.value(pos.piece_on(from), to_sq(m));
#endif
  }
}

void MovePicker::score_evasions() {
  // Try good captures ordered by MVV/LVA, then non-captures if destination square
  // is not under attack, ordered by history value, then bad-captures and quiet
  // moves with a negative SEE. This last group is ordered by the SEE score.
  Move m;
  int seeScore;

  if (lastMove < moves + 2)
      return;

  for (MoveStack* cur = moves; cur != lastMove; cur++)
  {
      m = cur->move;
      if ((seeScore = pos.see_sign(m)) < 0)
          cur->score = seeScore - History::MaxValue; // Be sure we are at the bottom
      else if (pos.is_capture(m))
          cur->score =  PieceValueMidgame[pos.piece_on(to_sq(m))]
#ifdef GPSFISH
                      - type_value_of_piece_on(pos.piece_moved(m)) + History::MaxValue; // XXX : why
#else
                      - type_of(pos.piece_moved(m)) + History::MaxValue;
#endif
      else
#ifdef GPSFISH
          cur->score = H.value(m.ptypeO(), to_sq(m));
#else
          cur->score = H.value(pos.piece_moved(m), to_sq(m));
#endif
  }
}


/// MovePicker::next_phase() generates, scores and sorts the next bunch of moves,
/// when there are no more moves to try for the current phase.

void MovePicker::next_phase() {

  curMove = moves;

  switch (++phase) {

  case TT_MOVE_S1: case TT_MOVE_S2: case TT_MOVE_S3: case TT_MOVE_S4: case TT_MOVE_S5:
      lastMove = curMove + 1;
      return;

  case CAPTURES_S1: case CAPTURES_S3: case CAPTURES_S4:
  case CAPTURES_S5: case CAPTURES_S6:
      lastMove = generate<MV_CAPTURE>(pos, moves);
      score_captures();
      return;

  case KILLERS_S1:
      curMove = killers;
      lastMove = curMove + 2;
      return;

  case QUIETS_1_S1:
      lastQuiet = lastMove = generate<MV_QUIET>(pos, moves);
      score_noncaptures();
      lastMove = std::partition(curMove, lastMove, has_positive_score);
      sort<MoveStack>(curMove, lastMove);
      return;

  case QUIETS_2_S1:
      curMove = lastMove;
      lastMove = lastQuiet;
      if (depth >= 3 * ONE_PLY)
          sort<MoveStack>(curMove, lastMove);
      return;

  case BAD_CAPTURES_S1:
      // Bad captures SEE value is already calculated so just pick them in order
      // to get SEE move ordering.
      curMove = badCaptures;
      lastMove = moves + MAX_MOVES;
      return;

  case EVASIONS_S2:
      assert(pos.in_check());
      lastMove = generate<MV_EVASION>(pos, moves);
      score_evasions();
      return;

  case QUIET_CHECKS_S3:
      lastMove = generate<MV_QUIET_CHECK>(pos, moves);
      return;

  case STOP_S1: case STOP_S2: case STOP_S3: case STOP_S4: case STOP_S5: case STOP_S6:
      lastMove = curMove + 1; // Avoid another next_phase() call
      return;

  default:
      assert(false);
  }
}


/// MovePicker::next_move() is the most important method of the MovePicker class.
/// It returns a new pseudo legal move every time it is called, until there
/// are no more moves left. It picks the move with the biggest score from a list
/// of generated moves taking care not to return the tt move if has already been
/// searched previously. Note that this function is not thread safe so should be
/// lock protected by caller when accessed through a shared MovePicker object.

Move MovePicker::next_move() {

  Move move;

  while (true)
  {
      while (curMove == lastMove)
          next_phase();

      switch (phase) {

      case TT_MOVE_S1: case TT_MOVE_S2: case TT_MOVE_S3: case TT_MOVE_S4: case TT_MOVE_S5:
          curMove++;
          return ttMove;
          break;

      case CAPTURES_S1:
          move = pick_best(curMove++, lastMove)->move;
          if (move != ttMove)
          {
              assert(captureThreshold <= 0); // Otherwise we cannot use see_sign()

              int seeScore = pos.see_sign(move);
              if (seeScore >= captureThreshold)
                  return move;

              // Losing capture, move it to the tail of the array
              (--badCaptures)->move = move;
              badCaptures->score = seeScore;
          }
          break;

      case KILLERS_S1:
          move = (curMove++)->move;
          if (   move != MOVE_NONE
              && pos.is_pseudo_legal(move)
              && move != ttMove
              && !pos.is_capture(move))
              return move;
          break;

      case QUIETS_1_S1:
      case QUIETS_2_S1:
          move = (curMove++)->move;
          if (   move != ttMove
              && move != killers[0].move
              && move != killers[1].move)
              return move;
          break;

      case BAD_CAPTURES_S1:
          move = pick_best(curMove++, lastMove)->move;
          return move;

      case EVASIONS_S2:
      case CAPTURES_S3: case CAPTURES_S4:
          move = pick_best(curMove++, lastMove)->move;
          if (move != ttMove)
              return move;
          break;

      case CAPTURES_S5:
           move = pick_best(curMove++, lastMove)->move;
           if (   move != ttMove
               && pos.see(move) > captureThreshold)
               return move;
           break;

      case CAPTURES_S6:
          move = pick_best(curMove++, lastMove)->move;
          if (to_sq(move) == recaptureSquare)
              return move;
          break;

      case QUIET_CHECKS_S3:
          move = (curMove++)->move;
          if (move != ttMove)
              return move;
          break;

      case STOP_S1: case STOP_S2: case STOP_S3: case STOP_S4: case STOP_S5: case STOP_S6:
          return MOVE_NONE;

      default:
          assert(false);
      }
  }
}
