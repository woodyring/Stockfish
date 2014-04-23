#if !defined(POSITION_TCC_INCLUDED)
#define POSITION_TCC_INCLUDED
#include "position.h"
#include "tt.h"
#include "osl/basic_type.h"
//#include "osl/misc/carray3d.h"

// defined in position.cpp
namespace Zobrist {

  extern osl::CArray3d<Key,COLOR_NB,osl::PTYPE_SIZE,osl::Square::SIZE> psq;
  extern Key side;
  extern Key exclusion;
}


template<typename F>
void Position::do_undo_move(Move m, StateInfo& newSt,F const& f){
  assert(is_ok());
  assert(move_is_ok(m));
  assert(&newSt != st);
  assert(move_is_legal(m));

  nodes++;
  Key key = st->key;
  struct ReducedStateInfo {
    int gamePly, pliesFromNull;
    Key key;
  };
  memcpy(&newSt, st, sizeof(ReducedStateInfo));

  newSt.previous = st;
  st = &newSt;

  // Save the current key to the history[] array, in order to be able to
  // detect repetition draws.
  //history[st->gamePly++] = key;

  // Update side to move
  key ^= Zobrist::side;

  st->pliesFromNull++;


  Color us = side_to_move();
  Color them = ~us;
  Square from = from_sq(m);
  Square to = to_sq(m);

  PieceType pt=m.ptype();
  osl::Ptype capture = m.capturePtype();
  st->capturedType = capture;
  if(capture!=osl::PTYPE_EMPTY){
    key -= Zobrist::psq[them][(int)capture][to.index()];
    key += Zobrist::psq[us][unpromote(capture)][Square::STAND().index()];
  }
  // Update hash key
  if(type_of(m)==PROMOTION)
    key += Zobrist::psq[us][(int)pt][to.index()]-Zobrist::psq[us][(int)unpromote(pt)][from.index()];
  else
    key += Zobrist::psq[us][(int)pt][to.index()]-Zobrist::psq[us][(int)pt][from.index()];

  st->key = key;
  prefetch((char*)TT.first_entry(key));
  int old_cont=continuous_check[us];
  CheckInfo ci(*this);
  continuous_check[us]=(gives_check(m,ci) ? old_cont+1 : 0);
  osl_state.makeUnmakeMove(m,f);
  continuous_check[us]=old_cont;
  st = st->previous;
}

template<typename F>
void Position::do_undo_null_move(StateInfo& backupSt, F const& f){
  assert(is_ok());
  backupSt.key      = st->key;
  backupSt.previous = st->previous;
  backupSt.pliesFromNull = st->pliesFromNull;
  st->previous = &backupSt;
  //history[st->gamePly++] = st->key;
  st->key ^= Zobrist::side;
  prefetch((char*)TT.first_entry(st->key));
  st->pliesFromNull = 0;
  Color us = side_to_move();
  int old_cont=continuous_check[us];
  continuous_check[us]=0;
  osl_state.makeUnmakePass(f);
  continuous_check[us]=old_cont;
  st->key      = backupSt.key;
  st->previous = backupSt.previous;
  st->pliesFromNull = backupSt.pliesFromNull;

  // Update the necessary information
  st->gamePly--;
}
#endif // !defined(POSITION_TCC_INCLUDED)
