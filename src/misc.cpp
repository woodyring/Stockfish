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

#include <iomanip>
#include <iostream>
#include <sstream>

#ifdef GPSFISH
# include "gpsshogi/revision.h"
#endif

#include "misc.h"
#include "thread.h"

using namespace std;

#ifdef GPSFISH
#endif

/// Version number. If Version is left empty, then compile date, in the
/// format DD-MM-YY, is shown in engine_info.
static const string Version = "DD";


/// engine_info() returns the full name of the current Stockfish version. This
/// will be either "Stockfish <Tag> DD-MM-YY" (where DD-MM-YY is the date when
/// the program was compiled) or "Stockfish <Version>", depending on whether
/// Version is empty.

const string engine_info(bool to_uci) {

  const string months("Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec");
  string month, day, year;
  stringstream s, date(__DATE__); // From compiler, format is "Sep 21 2008"

#ifdef GPSFISH
  s << "GPSfish " << Version << "+" << gpsshogi::gpsshogi_revision;
#else
  s << "Stockfish " << Version << setfill('0');
#endif

  if (Version.empty())
  {
      date >> month >> day >> year;
      s << setw(2) << day << setw(2) << (1 + months.find(month) / 4) << year.substr(2);
  }

  s << (Is64Bit ? " 64" : "")
    << (HasPopCnt ? " SSE4.2" : "")
    << (to_uci ? "\nid author ": " by ")
#ifdef GPSFISH
    << "Team GPS (GPSshogi) / Tord Romstad, Marco Costalba and Joona Kiiski (Stockfish)";
#else
    << "Tord Romstad, Marco Costalba and Joona Kiiski";
#endif

  return s.str();
}


/// Debug functions used mainly to collect run-time statistics

static uint64_t hits[2], means[2];

void dbg_hit_on(bool b) { ++hits[0]; if (b) ++hits[1]; }
void dbg_hit_on_c(bool c, bool b) { if (c) dbg_hit_on(b); }
void dbg_mean_of(int v) { ++means[0]; means[1] += v; }

void dbg_print() {

  if (hits[0])
      cerr << "Total " << hits[0] << " Hits " << hits[1]
           << " hit rate (%) " << 100 * hits[1] / hits[0] << endl;

  if (means[0])
      cerr << "Total " << means[0] << " Mean "
           << (double)means[1] / means[0] << endl;
}


/// Our fancy logging facility. The trick here is to replace cin.rdbuf() and
/// cout.rdbuf() with two Tie objects that tie cin and cout to a file stream. We
/// can toggle the logging of std::cout and std:cin at runtime while preserving
/// usual i/o functionality and without changing a single line of code!
/// Idea from http://groups.google.com/group/comp.lang.c++/msg/1d941c0f26ea0d81

struct Tie: public streambuf { // MSVC requires splitted streambuf for cin and cout

  Tie(streambuf* b, ofstream* f) : buf(b), file(f) {}

  int sync() { return file->rdbuf()->pubsync(), buf->pubsync(); }
  int overflow(int c) { return log(buf->sputc((char)c), "<< "); }
  int underflow() { return buf->sgetc(); }
  int uflow() { return log(buf->sbumpc(), ">> "); }

  streambuf* buf;
  ofstream* file;

  int log(int c, const char* prefix) {

    static int last = '\n';

    if (last == '\n')
        file->rdbuf()->sputn(prefix, 3);

    return last = file->rdbuf()->sputc((char)c);
  }
};

class Logger {

  Logger() : in(cin.rdbuf(), &file), out(cout.rdbuf(), &file) {}
 ~Logger() { start(false); }

  ofstream file;
  Tie in, out;

public:
  static void start(bool b) {

    static Logger l;

    if (b && !l.file.is_open())
    {
        l.file.open("io_log.txt", ifstream::out | ifstream::app);
        cin.rdbuf(&l.in);
        cout.rdbuf(&l.out);
    }
    else if (!b && l.file.is_open())
    {
        cout.rdbuf(l.out.buf);
        cin.rdbuf(l.in.buf);
        l.file.close();
    }
  }
};


/// Used to serialize access to std::cout to avoid multiple threads to write at
/// the same time.

std::ostream& operator<<(std::ostream& os, SyncCout sc) {

  static Mutex m;

  if (sc == io_lock)
      m.lock();

  if (sc == io_unlock)
      m.unlock();

  return os;
}


/// Trampoline helper to avoid moving Logger to misc.h
void start_logger(bool b) { Logger::start(b); }


/// timed_wait() waits for msec milliseconds. It is mainly an helper to wrap
/// conversion from milliseconds to struct timespec, as used by pthreads.

void timed_wait(WaitCondition& sleepCond, Lock& sleepLock, int msec) {

#ifdef _WIN32
  int tm = msec;
#else
  timespec ts, *tm = &ts;
  uint64_t ms = Time::now() + msec;

  ts.tv_sec = ms / 1000;
  ts.tv_nsec = (ms % 1000) * 1000000LL;
#endif

  cond_timedwait(sleepCond, sleepLock, tm);
}


/// prefetch() preloads the given address in L1/L2 cache. This is a non
/// blocking function and do not stalls the CPU waiting for data to be
/// loaded from memory, that can be quite slow.
#ifdef NO_PREFETCH

void prefetch(char*) {}

#else

void prefetch(char* addr) {

#  if defined(__INTEL_COMPILER)
   // This hack prevents prefetches to be optimized away by
   // Intel compiler. Both MSVC and gcc seems not affected.
   __asm__ ("");
#  endif

#  if defined(__INTEL_COMPILER) || defined(_MSC_VER)
  _mm_prefetch(addr, _MM_HINT_T0);
#  else
  __builtin_prefetch(addr);
#  endif
}

#endif
