#include "osl/book/bookInMemory.h"
#include "osl/random.h"
#include "notation.h"

using osl::book::BookInMemory;

PolyglotBook::PolyglotBook() {}

PolyglotBook::~PolyglotBook() {}

Move PolyglotBook::probe(const Position& pos, const std::string& fName, bool pickBest)
{
    const BookInMemory& book = BookInMemory::instance();
    osl::HashKey key(pos.osl_state);
    osl::MoveVector moves;

    book.find(key, moves);

    if(moves.empty()) return MOVE_NONE;

    if(pickBest)
        return moves[0];
    else {
        for( size_t i = 0 ; i < moves.size() ; i++ ) {
            sync_cout << "info pv " << move_to_uci(moves[i],false) << sync_endl;
        }
        return moves[osl::time_seeded_random()%moves.size()];
    }
}

