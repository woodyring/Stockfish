#include "osl/eval/ml/openMidEndingEval.h"

Value evaluate(const Position& pos, Value& margin) {
    margin=VALUE_ZERO;
    int iret=pos.eval->value();
    assert(iret==eval_t(pos.osl_state,false).value());
    Value ret=(Value)(iret/100);
    assert(-VALUE_MATE<ret && ret<VALUE_MATE);
    if(pos.side_to_move()==BLACK)
        return ret;
    else
        return -ret;
}

std::string trace_evaluate(const Position& pos){
    return "";
}

void read_evaluation_uci_options(Color sideToMove){
}

