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


