#ifndef MINIMAL
#  define MINIMAL
#endif
#ifndef NDEBUG
#  define NDEBUG
#endif
#define GPSFISHONE

#include "../../osl/core/osl/checkmate/immediateCheckmate.cc"
#include "../../osl/core/osl/checkmate/immediateCheckmateTable.cc"
#include "../../osl/core/osl/checkmate/fixedDepthSearcher.cc"
#include "../../osl/core/osl/basic_type.cc"
#include "../../osl/core/osl/numEffectState.cc"
#include "../../osl/core/osl/simpleState.cc"
#include "../../osl/core/osl/container.cc"
#include "../../osl/core/osl/bits/boardMask.cc"
#include "../../osl/core/osl/enterKing.cc"
#include "../../osl/core/osl/eval/openMidEndingEval.cc"
#include "../../osl/core/osl/eval/ptypeEval.cc"
#include "../../osl/core/osl/eval/see.cc"
#include "../../osl/core/osl/hashKey.cc"
#include "../../osl/core/osl/bits/pieceTable.cc"
#include "../../osl/core/osl/progress.cc"
#include "../../osl/core/osl/bits/ptypeTable.cc"
#include "../../osl/core/osl/csa.cc"
#include "../../osl/core/osl/book/bookInMemory.cc"
#include "../../osl/core/osl/usi.cc"
#include "../../osl/core/osl/bits/squareCompressor.cc"
#include "../../osl/core/osl/bits/bitXmask.cc"
#include "../../osl/core/osl/bits/effectedNumTable.cc"
#include "../../osl/core/osl/bits/numSimpleEffect.cc"
#include "../../osl/core/osl/bits/boardTable.cc"
#include "../../osl/core/osl/bits/centering5x3.cc"
#include "../../osl/core/osl/additionalEffect.cc"
#include "../../osl/core/osl/eval/king8.cc"
#include "../../osl/core/osl/eval/kingTable.cc"
#include "../../osl/core/osl/eval/majorPiece.cc"
#include "../../osl/core/osl/eval/minorPiece.cc"
#include "../../osl/core/osl/eval/mobility.cc"
#include "../../osl/core/osl/eval/piecePair.cc"
#include "../../osl/core/osl/eval/piecePairKing.cc"
#include "../../osl/core/osl/eval/eval_pieceStand.cc"
#include "../../osl/core/osl/eval/eval_pin.cc"
#include "../../osl/core/osl/eval/weights.cc"
#include "../../osl/core/osl/bits/binaryIO.cc"
#include "../../osl/core/osl/oslConfig.cc"
#include "../../osl/core/osl/bits/pieceStand.cc"
#include "../../osl/core/osl/book/openingBook.cc"
#include "../../osl/core/osl/random.cc"
#include "../../osl/core/osl/mobility/mobilityTable.cc"
#include "../../osl/core/osl/book/compactBoard.cc"
#include "../../osl/core/osl/bits/king8Info.cc"
#include "../../osl/core/osl/move_classifier/kingOpenMove.cc"

#include "tables.cc"

//#include "move.cpp"
#include "notation.cpp"
#include "movegen.cpp"
#include "position.cpp"
#include "tt.cpp"
#include "movepick.cpp"
#include "search.cpp"
#include "book.cpp"
#include "thread.cpp"
#include "benchmark.cpp"
#include "misc.cpp"
#include "timeman.cpp"
#include "evaluate.cpp"
#include "ucioption.cpp"
#include "uci.cpp"
#include "main.cpp"
