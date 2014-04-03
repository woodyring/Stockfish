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

#if !defined(TT_H_INCLUDED)
#define TT_H_INCLUDED

#ifdef GPSFISH
#include "osl/squareCompressor.h"
using osl::SquareCompressor;
#include "position.h"
#endif

#include "misc.h"
#include "types.h"

/// The TTEntry is the class of transposition table entries
///
/// A TTEntry needs 128 bits to be stored
///
/// bit  0-31: key
/// bit 32-63: data
/// bit 64-79: value
/// bit 80-95: depth
/// bit 96-111: static value
/// bit 112-127: margin of static value
///
/// the 32 bits of the data field are so defined
///
/// bit  0-15: move
/// bit 16-20: not used
/// bit 21-22: value type
/// bit 23-31: generation

#ifdef GPSFISH
enum Move16 {MOVE16_NONE = 0};
static inline Move16 toMove16(Move m){
  Move16 move16;
  if(m==MOVE_NONE) return MOVE16_NONE;
  if(m.isDrop())
    move16=Move16(0x80+(uint16_t)m.ptype()+((SquareCompressor::compress(m.to()))<<8));
  else if(m.isPromotion()){
    move16=Move16(SquareCompressor::compress(m.from())+(SquareCompressor::compress(m.to())<<8)+0x8000);
  }
  else{
    move16=Move16(SquareCompressor::compress(m.from())+(SquareCompressor::compress(m.to())<<8));
  }
  return move16;
}
static inline Move fromMove16(Move16 move16,Position const& pos) {
  if(move16==MOVE16_NONE) return MOVE_NONE;
  Color turn=pos.side_to_move();
  Square to=SquareCompressor::melt((move16>>8)&0x7f);
  if((move16&0x80)!=0){
    Ptype ptype=(Ptype)(move16-0x80);
    return osl::Move(to,ptype,turn);
  }
  Square from=SquareCompressor::melt(move16&0x7f);
  Ptype ptype=type_of(pos.piece_on(from));
  Ptype capture_ptype=type_of(pos.piece_on(to));
  bool is_promote=(move16&0x8000)!=0;
  if(is_promote)
    return osl::Move(from,to,promote(ptype),capture_ptype,true,turn);
  else
    return osl::Move(from,to,ptype,capture_ptype,false,turn);
}
#endif
class TTEntry {

public:
#ifdef GPSFISH
  void save(uint32_t k, Value v, Bound b, Depth d, Move m, int g, Value ev, Value em) {
    return save(k,v,b,d,toMove16(m),g,ev,em);
  }
  void save(uint32_t k, Value v, Bound b, Depth d, Move16 m, int g, Value ev, Value em) {
#else
  void save(uint32_t k, Value v, Bound b, Depth d, Move m, int g, Value ev, Value em) {
#endif

    key32        = (uint32_t)k;
    move16       = (uint16_t)m;
    bound        = (uint8_t)b;
    generation8  = (uint8_t)g;
    value16      = (int16_t)v;
    depth16      = (int16_t)d;
    evalValue    = (int16_t)ev;
    evalMargin   = (int16_t)em;
  }

  void set_generation(int g) { generation8 = (uint8_t)g; }

  uint32_t key() const      { return key32; }
  Depth depth() const       { return (Depth)depth16; }
#ifdef GPSFISH
  Move16 move16Val() const  { return (Move16)move16; }
  Move move(Position const& pos) const { return fromMove16((Move16)move16,pos); }
#else
  Move move() const         { return (Move)move16; }
#endif
  Value value() const       { return (Value)value16; }
  Bound type() const        { return (Bound)bound; }
  int generation() const    { return (int)generation8; }
  Value eval_value() const  { return (Value)evalValue; }
  Value eval_margin() const { return (Value)evalMargin; }

private:
  uint32_t key32;
  uint16_t move16;
  uint8_t bound, generation8;
  int16_t value16, depth16, evalValue, evalMargin;
};


/// A TranspositionTable consists of a power of 2 number of clusters and each
/// cluster consists of ClusterSize number of TTEntry. Each non-empty entry
/// contains information of exactly one position. Size of a cluster shall not be
/// bigger than a cache line size. In case it is less, it should be padded to
/// guarantee always aligned accesses.

class TranspositionTable {

  static const unsigned ClusterSize = 4; // A cluster is 64 Bytes

public:
 ~TranspositionTable() { delete [] table; }
  void new_search() { generation++; }

  TTEntry* probe(const Key key) const;
  TTEntry* first_entry(const Key key) const;
  void refresh(const TTEntry* tte) const;
  void set_size(size_t mbSize);
  void clear();
#ifdef GPSFISH
  void store(const Key key, Value v, Bound b, Depth d, Move16 m, Value statV, Value kingD);
  void store(const Key key, Value v, Bound b, Depth d, Move m, Value statV, Value kingD);
#else
  void store(const Key key, Value v, Bound type, Depth d, Move m, Value statV, Value kingD);
#endif

#ifdef GPSFISH
  size_t get_hashfull() { return 1000ll*used/(hashMask+ClusterSize)/ClusterSize; }
#endif
private:
  uint32_t hashMask;
  TTEntry* table;
  uint8_t generation; // Size must be not bigger then TTEntry::generation8
#ifdef GPSFISH
  size_t used;
#endif
};

extern TranspositionTable TT;


/// TranspositionTable::first_entry() returns a pointer to the first entry of
/// a cluster given a position. The lowest order bits of the key are used to
/// get the index of the cluster.

inline TTEntry* TranspositionTable::first_entry(const Key key) const {

  return table + ((uint32_t)key & hashMask);
}


/// TranspositionTable::refresh() updates the 'generation' value of the TTEntry
/// to avoid aging. Normally called after a TT hit.

inline void TranspositionTable::refresh(const TTEntry* tte) const {

  const_cast<TTEntry*>(tte)->set_generation(generation);
}

#endif // !defined(TT_H_INCLUDED)
