
struct Store{
    ExtMove* mlist;
    Store(ExtMove* mlist_) :mlist(mlist_){}
    void simpleMove(Square /*from*/,Square /*to*/,Ptype /*ptype*/, bool /*isPromote*/,Player /*p*/,Move move){
        (*mlist++).move = move;
    }
    void unknownMove(Square /*from*/,Square /*to*/,osl::Piece /*p1*/,Ptype /*ptype*/,bool /*isPromote*/,Player /*p*/,Move move)
    {
        (*mlist++).move = move;
    }
    void dropMove(Square /*to*/,Ptype /*ptype*/,Player /*p*/,Move move)
    {
        (*mlist++).move = move;
    }
    // old interfaces
    void simpleMove(Square from,Square to,Ptype ptype,
            bool isPromote,Player p)
    {
        simpleMove(from,to,ptype,isPromote,p,
                Move(from,to,ptype,osl::PTYPE_EMPTY,isPromote,p));
    }
    void unknownMove(Square from,Square to,osl::Piece captured,
            Ptype ptype,bool isPromote,Player p)
    {
        unknownMove(from,to,captured,ptype,isPromote,p,
                Move(from,to,ptype,captured.ptype(),isPromote,p));
    }
    void dropMove(Square to,Ptype ptype,Player p)
    {
        dropMove(to,ptype,p,
                Move(to,ptype,p));
    }
};

struct NoCaptureStore{
    ExtMove* mlist;
    NoCaptureStore(ExtMove* mlist_) :mlist(mlist_){}
    void simpleMove(Square /*from*/,Square /*to*/,Ptype /*ptype*/, bool isPromote,Player /*p*/,Move move){
#ifdef PROMOTE_AS_CAPTURE
        if(!isPromote)
#endif
            (*mlist++).move = move;
    }
    void unknownMove(Square /*from*/,Square /*to*/,osl::Piece p1,Ptype /*ptype*/,bool isPromote,Player /*p*/,Move move)
    {
#ifdef PROMOTE_AS_CAPTURE
        if(!isPromote && p1.isEmpty())
#else
            if(p1.isEmpty())
#endif
                (*mlist++).move = move;
    }
    void dropMove(Square /*to*/,Ptype /*ptype*/,Player /*p*/,Move move)
    {
        (*mlist++).move = move;
    }
    // old interfaces
    void simpleMove(Square from,Square to,Ptype ptype,
            bool isPromote,Player p)
    {
#ifdef PROMOTE_AS_CAPTURE
        if(!isPromote)
#endif
            (*mlist++).move = Move(from,to,ptype,osl::PTYPE_EMPTY,isPromote,p);
    }
    void unknownMove(Square from,Square to,osl::Piece captured,
            Ptype ptype,bool isPromote,Player p)
    {
#ifdef PROMOTE_AS_CAPTURE
        if(!isPromote && captured.isEmpty())
#else
            if(captured.isEmpty())
#endif
                (*mlist++).move = Move(from,to,ptype,captured.ptype(),isPromote,p);
    }
    void dropMove(Square to,Ptype ptype,Player p)
    {
        (*mlist++).move = Move(to,ptype,p);
    }
};

template<osl::Player P,GenType Type>
ExtMove* generateC(const Position& pos, ExtMove* mlist) {
    const osl::Player altP=alt(P);
    if(Type==CAPTURES){
        Store store(mlist);
        for(int num=0;num<osl::Piece::SIZE;num++){
            osl::Piece p=pos.osl_state.pieceOf(num);
            if(p.isOnBoardByOwner<altP>())
                osl::move_generator::Capture<Store>::generate<P>(pos.osl_state,p.square(),store);
        }
#ifdef PROMOTE_AS_CAPTURE
        osl::move_action::NotKingOpenFilter<P,Store> not_king_open(pos.osl_state,store);
        osl::move_generator::Promote<P,true>::generateMoves(pos.osl_state,not_king_open);
#endif
        return store.mlist;
    }
    else if(Type==QUIETS){
        NoCaptureStore store(mlist);
        osl::move_generator::AllMoves<NoCaptureStore>::generate<P>(pos.osl_state,store);
        return store.mlist;
    }
    else if(Type==NON_EVASIONS){
        Store store(mlist);
        osl::move_generator::AllMoves<Store>::generate<P>(pos.osl_state,store);
        return store.mlist;
    }
    else if(Type==QUIET_CHECKS){
        NoCaptureStore store(mlist);
        osl::move_generator::AddEffectWithEffect<NoCaptureStore>::generate<P,true>(pos.osl_state,pos.king_square(altP),store);
        return store.mlist;
    }
    else{
        assert(Type==EVASIONS);
        Store store(mlist);
        osl::move_generator::Escape<Store>::generateKingEscape<P,false>(pos.osl_state,store);
        return store.mlist;
    }
}

