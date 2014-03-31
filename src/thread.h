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

#if !defined(THREAD_H_INCLUDED)
#define THREAD_H_INCLUDED

#include <vector>

#ifndef GPSFISH
#include "material.h"
#endif
#include "movepick.h"
#ifndef GPSFISH
#include "pawns.h"
#endif
#include "position.h"
#include "search.h"

const int MAX_THREADS = 64; // Because SplitPoint::slavesMask is a uint64_t
const int MAX_SPLITPOINTS_PER_THREAD = 8;

struct Mutex {
  Mutex() { lock_init(l); }
 ~Mutex() { lock_destroy(l); }

  void lock() { lock_grab(l); }
  void unlock() { lock_release(l); }

private:
  friend struct ConditionVariable;

  Lock l;
};

struct ConditionVariable {
  ConditionVariable() { cond_init(c); }
 ~ConditionVariable() { cond_destroy(c); }

  void wait(Mutex& m) { cond_wait(c, m.l); }
  void wait_for(Mutex& m, int ms) { timed_wait(c, m.l, ms); }
  void notify_one() { cond_signal(c); }

private:
  WaitCondition c;
};

class Thread;

struct SplitPoint {

  // Const data after split point has been setup
  const Position* pos;
  const Search::Stack* ss;
  Depth depth;
  Value beta;
  int nodeType;
  Thread* master;
  Move threatMove;

  // Const pointers to shared data
  MovePicker* mp;
  SplitPoint* parent;

  // Shared data
  Mutex mutex;
  Position* activePositions[MAX_THREADS];
  volatile uint64_t slavesMask;
  volatile int64_t nodes;
  volatile Value alpha;
  volatile Value bestValue;
  volatile Move bestMove;
  volatile int moveCount;
  volatile bool cutoff;
};


/// Thread struct keeps together all the thread related stuff like locks, state
/// and especially split points. We also use per-thread pawn and material hash
/// tables so that once we get a pointer to an entry its life time is unlimited
/// and we don't have to care about someone changing the entry under our feet.

class Thread {

public:
  Thread();
  virtual ~Thread();

  virtual void idle_loop();
  void notify_one();
  bool cutoff_occurred() const;
  bool is_available_to(Thread* master) const;
  void wait_for(volatile const bool& b);

  SplitPoint splitPoints[MAX_SPLITPOINTS_PER_THREAD];
#ifndef GPSFISH
  Material::Table materialTable;
  Endgames endgames;
  Pawns::Table pawnsTable;
#endif
  size_t idx;
  int maxPly;
  Mutex mutex;
  ConditionVariable sleepCondition;
  NativeHandle handle;
  SplitPoint* volatile curSplitPoint;
  volatile int splitPointsCnt;
  volatile bool is_searching;
  volatile bool do_exit;
};

struct TimerThread : public Thread {
  TimerThread() : msec(0) {}
  virtual void idle_loop();
  int msec;
};

struct MainThread : public Thread {
  MainThread() : is_finished(false) {} // Avoid a race with start_searching()
  virtual void idle_loop();
  volatile bool is_finished;
};


/// ThreadPool class handles all the threads related stuff like init, starting,
/// parking and, the most important, launching a slave thread at a split point.
/// All the access to shared thread data is done through this class.

class ThreadPool {

public:
  void init(); // No c'tor and d'tor, threads rely on globals that should
  void exit(); // be initialized and valid during the whole thread lifetime.

  Thread& operator[](size_t id) { return *threads[id]; }
  int min_split_depth() const { return minimumSplitDepth; }
  size_t size() const { return threads.size(); }
  MainThread* main_thread() { return static_cast<MainThread*>(threads[0]); }
  TimerThread* timer_thread() { return timer; }

  void read_uci_options();
  bool available_slave_exists(Thread* master) const;
  void wait_for_search_finished();
  void start_searching(const Position&, const Search::LimitsType&,
                       const std::vector<Move>&, Search::StateStackPtr&);

  template <bool Fake>
  Value split(Position& pos, Search::Stack* ss, Value alpha, Value beta, Value bestValue, Move* bestMove,
              Depth depth, Move threatMove, int moveCount, MovePicker& mp, int nodeType);
private:
  friend class Thread;
  friend struct MainThread;
  friend void check_time();

  std::vector<Thread*> threads;
  TimerThread* timer;
  Mutex mutex;
  ConditionVariable sleepCondition;
  Depth minimumSplitDepth;
  int maxThreadsPerSplitPoint;
public:
  bool sleepWhileIdle;
};

extern ThreadPool Threads;

#endif // !defined(THREAD_H_INCLUDED)
