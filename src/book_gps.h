#include "osl/book/bookInMemory.h"
#include "osl/random.h"
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
    else
        return moves[osl::time_seeded_random()%moves.size()];
}

