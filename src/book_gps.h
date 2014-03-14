#include "osl/record/opening/bookInMemory.h"
#include "osl/misc/random.h"
using osl::record::opening::BookInMemory;
Book::Book() {}
Book::~Book() {}
void Book::open(const std::string& fileName){}
void Book::close(){}
Move Book::get_move(const Position& pos, bool findBestMove){
  const BookInMemory& book = BookInMemory::instance();
  osl::hash::HashKey key(pos.osl_state);
  osl::container::MoveVector moves;
  book.find(key, moves);
  if(moves.empty()) return MOVE_NONE;
  if(findBestMove)
    return moves[0];
  else
    return moves[osl::time_seeded_random()%moves.size()];
}

