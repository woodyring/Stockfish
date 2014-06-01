/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2014 Marco Costalba, Joona Kiiski, Tord Romstad

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

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <sstream>

#ifdef GPSFISH
#  include <fstream>
#  ifdef __APPLE__
#    include <sys/sysctl.h>
#  endif
#  ifdef _WIN32
#    include <windows.h>
#  endif
#endif

#include "evaluate.h"
#include "misc.h"
#include "thread.h"
#include "tt.h"
#include "ucioption.h"

using std::string;

UCI::OptionsMap Options; // Global object

namespace UCI {

/// 'On change' actions, triggered by an option's value change
void on_logger(const Option& o) { start_logger(o); }
#ifndef GPSFISH
void on_eval(const Option&) { Eval::init(); }
#endif
void on_threads(const Option&) { Threads.read_uci_options(); }
void on_hash_size(const Option& o) { TT.resize(o); }
void on_clear_hash(const Option&) { TT.clear(); }


/// Our case insensitive less() function as required by UCI protocol
bool ci_less(char c1, char c2) { return tolower(c1) < tolower(c2); }

bool CaseInsensitiveLess::operator() (const string& s1, const string& s2) const {
  return std::lexicographical_compare(s1.begin(), s1.end(), s2.begin(), s2.end(), ci_less);
}


#ifdef GPSFISH
static size_t get_memory()
{
  size_t memory = 32;
#  ifdef __APPLE__
  {
    int mib[2];
    size_t usermem;
    size_t len=sizeof(usermem);
    mib[0] = CTL_HW;
    mib[1] = HW_USERMEM;
    if (sysctl(mib, 2, &usermem, &len, NULL, 0) == 0
       && len == sizeof(usermem)) {
      memory = std::min((size_t)2048, usermem/1024/1024/4);
    }
  }
#  elif defined (_WIN32)
  {
    MEMORYSTATUSEX statex;
    statex.dwLength = sizeof(statex);
    GlobalMemoryStatusEx(&statex);
    const size_t bytes = statex.ullTotalPhys; // in bytes
    memory = std::min((size_t)2048, std::max(memory, bytes/1024/1024/4));
  }
#  else
  {
    std::string name, unit;
    size_t value;
    std::ifstream is("/proc/meminfo");
    if (is >> name >> value >> unit
       && name == "MemTotal:" && unit == "kB")
      memory = std::min((size_t)2048, std::max(memory, value/1024/4));
  }
#  endif

  return memory;
}
#endif

/// init() initializes the UCI options to their hard-coded default values

void init(OptionsMap& o) {

  o["Write Debug Log"]          << Option(false, on_logger);
  o["Write Search Log"]         << Option(false);
  o["Search Log Filename"]      << Option("SearchLog.txt");
#ifndef GPSFISH
  o["Book File"]                << Option("book.bin");
#endif
  o["Best Book Move"]           << Option(false);

#ifndef GPSFISH
  o["Contempt Factor"]          << Option(0, -50,  50);
  o["Mobility (Midgame)"]       << Option(100, 0, 200, on_eval);
  o["Mobility (Endgame)"]       << Option(100, 0, 200, on_eval);
  o["Pawn Structure (Midgame)"] << Option(100, 0, 200, on_eval);
  o["Pawn Structure (Endgame)"] << Option(100, 0, 200, on_eval);
  o["Passed Pawns (Midgame)"]   << Option(100, 0, 200, on_eval);
  o["Passed Pawns (Endgame)"]   << Option(100, 0, 200, on_eval);
  o["Space"]                    << Option(100, 0, 200, on_eval);
  o["Aggressiveness"]           << Option(100, 0, 200, on_eval);
  o["Cowardice"]                << Option(100, 0, 200, on_eval);
#endif
  o["Min Split Depth"]          << Option(0, 0, 12, on_threads);
  o["Threads"]                  << Option(1, 1, MAX_THREADS, on_threads);
  o["Idle Threads Sleep"]       << Option(true);

#ifdef GPSFISH
  o["Hash"]                     << Option(get_memory(), 1, 16384, on_hash_size);
#else
  o["Hash"]                     << Option(32, 1, 16384, on_hash_size);
#endif
  o["Clear Hash"]               << Option(on_clear_hash);
#ifdef GPSFISH
  o["Ponder"]                   << Option(false);
  o["OwnBook"]                  << Option(true);
#else
  o["Ponder"]                   << Option(true);
  o["OwnBook"]                  << Option(false);
#endif

  o["MultiPV"]                  << Option(1, 1, 500);
  o["Skill Level"]              << Option(20, 0, 20);
#ifdef GPSFISH
  o["Emergency Move Horizon"]   << Option(50, 0, 60);
  o["Emergency Base Time"]      << Option(20000, 0, 30000);
  o["Emergency Move Time"]      << Option(1000, 0, 5000);
#else
  o["Emergency Move Horizon"]   << Option(40, 0, 50);
  o["Emergency Base Time"]      << Option(60, 0, 30000);
  o["Emergency Move Time"]      << Option(30, 0, 5000);

#endif
  o["Minimum Thinking Time"]    << Option(20, 0, 5000);
  o["Slow Mover"]               << Option(80, 10, 1000);
#ifndef GPSFISH
  o["UCI_Chess960"]             << Option(false);
#endif

#ifdef GPSFISH
  o["DrawValue"]                << Option(0, -30000, 30000);
  o["Resign"]                   << Option(32765, 1000, 32765);
#endif
}

#ifdef GPSFISH
std::string strReplace (const std::string& orig, const std::string& from, const std::string& to) {
  std::string str(orig);
  std::string::size_type pos = 0;
  while(pos = str.find(from, pos), pos != std::string::npos) {
      str.replace(pos, from.length(), to);
      pos += to.length();
  }
  return str;
}
#endif

/// operator<<() is used to print all the options default values in chronological
/// insertion order (the idx field) and in the format defined by the UCI protocol.

std::ostream& operator<<(std::ostream& os, const OptionsMap& om) {

  for (size_t idx = 0; idx < om.size(); ++idx)
      for (OptionsMap::const_iterator it = om.begin(); it != om.end(); ++it)
          if (it->second.idx == idx)
          {
              const Option& o = it->second;
#ifdef GPSFISH
              // shogidokoro hack
              std::string str = strReplace(it->first," ","_");
              os << "\noption name " << str << " type " << o.type;
#else
              os << "\noption name " << it->first << " type " << o.type;
#endif

              if (o.type != "button")
                  os << " default " << o.defaultValue;

              if (o.type == "spin")
                  os << " min " << o.min << " max " << o.max;

              break;
          }
  return os;
}


/// Option class constructors and conversion operators

Option::Option(const char* v, OnChange f) : type("string"), min(0), max(0), on_change(f)
{ defaultValue = currentValue = v; }

Option::Option(bool v, OnChange f) : type("check"), min(0), max(0), on_change(f)
{ defaultValue = currentValue = (v ? "true" : "false"); }

Option::Option(OnChange f) : type("button"), min(0), max(0), on_change(f)
{}

Option::Option(int v, int minv, int maxv, OnChange f) : type("spin"), min(minv), max(maxv), on_change(f)
{ std::ostringstream ss; ss << v; defaultValue = currentValue = ss.str(); }


Option::operator int() const {
  assert(type == "check" || type == "spin");
  return (type == "spin" ? atoi(currentValue.c_str()) : currentValue == "true");
}

Option::operator std::string() const {
  assert(type == "string");
  return currentValue;
}


/// operator<<() inits options and assigns idx in the correct printing order

void Option::operator<<(const Option& o) {

  static size_t index = 0;

  *this = o;
  idx = index++;
}


/// operator=() updates currentValue and triggers on_change() action. It's up to
/// the GUI to check for option's limits, but we could receive the new value from
/// the user by console window, so let's check the bounds anyway.

Option& Option::operator=(const string& v) {

  assert(!type.empty());

  if (   (type != "button" && v.empty())
      || (type == "check" && v != "true" && v != "false")
      || (type == "spin" && (atoi(v.c_str()) < min || atoi(v.c_str()) > max)))
      return *this;

  if (type != "button")
      currentValue = v;

  if (on_change)
      on_change(*this);

  return *this;
}

} // namespace UCI
