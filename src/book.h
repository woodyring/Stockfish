/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2012 Marco Costalba, Joona Kiiski, Tord Romstad

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

#if !defined(BOOK_H_INCLUDED)
#define BOOK_H_INCLUDED

#include <fstream>
#include <string>

#include "position.h"
#include "rkiss.h"


#ifndef GPSFISH
/// A Polyglot book is a series of "entries" of 16 bytes. All integers are
/// stored highest byte first (regardless of size). The entries are ordered
/// according to key. Lowest key first.
struct BookEntry {
  uint64_t key;
  uint16_t move;
  uint16_t count;
  uint32_t learn;
};
#endif


class Book : private std::ifstream {
public:
  Book();
  ~Book();
  Move probe(const Position& pos, const std::string& fName, bool pickBest);

private:
#ifndef GPSFISH
  template<typename T> Book& operator>>(T& n);

  bool open(const char* fName);
  size_t find_first(uint64_t key);

  RKISS RKiss;
  std::string fileName;
#endif
};

#endif // !defined(BOOK_H_INCLUDED)
