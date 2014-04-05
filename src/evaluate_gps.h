#include "osl/eval/ml/openMidEndingEval.h"

namespace Eval {

Value evaluate(const Position& pos)
{
    int iret=pos.eval->value();
    assert(iret==eval_t(pos.osl_state,false).value());

    Value ret=(Value)(iret/100);
    assert(-VALUE_MATE<ret && ret<VALUE_MATE);

    if(pos.side_to_move()==BLACK)
        return ret;
    else
        return -ret;
}

std::string trace(const Position& pos){
    return "";
}

}
