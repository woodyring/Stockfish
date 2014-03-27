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

#if !defined(LOCK_H_INCLUDED)
#define LOCK_H_INCLUDED

#if !defined(_MSC_VER) && !defined(_WIN32)

#  include <pthread.h>

typedef pthread_mutex_t Lock;
typedef pthread_cond_t WaitCondition;
typedef pthread_t ThreadHandle;

#  define lock_init(x) pthread_mutex_init(&(x), NULL)
#  define lock_grab(x) pthread_mutex_lock(&(x))
#  define lock_release(x) pthread_mutex_unlock(&(x))
#  define lock_destroy(x) pthread_mutex_destroy(&(x))
#  define cond_destroy(x) pthread_cond_destroy(&(x))
#  define cond_init(x) pthread_cond_init(&(x), NULL)
#  define cond_signal(x) pthread_cond_signal(&(x))
#  define cond_wait(x,y) pthread_cond_wait(&(x),&(y))
#  define cond_timedwait(x,y,z) pthread_cond_timedwait(&(x),&(y),z)
#ifdef GPSFISH
#  define thread_create(x,f,id) { \
    pthread_attr_t attr; \
    pthread_attr_init(&attr); \
    pthread_attr_setstacksize(&attr,1024*1024*16); \
    !pthread_create(&(x),NULL,f,&(id)); \
}
#else
#  define thread_create(x,f,id) !pthread_create(&(x),NULL,f,&(id))
#endif
#  define thread_join(x) pthread_join(x, NULL)

#else

#ifndef NOMINMAX 
#define NOMINMAX // disable macros min() and max()
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#undef WIN32_LEAN_AND_MEAN
#undef NOMINMAX

// We use critical sections on Windows to support Windows XP and older versions,
// unfortunatly cond_wait() is racy between lock_release() and WaitForSingleObject()
// but apart from this they have the same speed performance of SRW locks.
typedef CRITICAL_SECTION Lock;
typedef HANDLE WaitCondition;
typedef HANDLE ThreadHandle;

#  define lock_init(x) InitializeCriticalSection(&(x))
#  define lock_grab(x) EnterCriticalSection(&(x))
#  define lock_release(x) LeaveCriticalSection(&(x))
#  define lock_destroy(x) DeleteCriticalSection(&(x))
#  define cond_init(x) { x = CreateEvent(0, FALSE, FALSE, 0); }
#  define cond_destroy(x) CloseHandle(x)
#  define cond_signal(x) SetEvent(x)
#  define cond_wait(x,y) { lock_release(y); WaitForSingleObject(x, INFINITE); lock_grab(y); }
#  define cond_timedwait(x,y,z) { lock_release(y); WaitForSingleObject(x,z); lock_grab(y); }
#ifdef GPSFISH
#  define thread_create(x,f,id) (x = CreateThread(NULL,16*1024*1024,f,&(id),0,NULL), x != NULL)
#else
#  define thread_create(x,f,id) (x = CreateThread(NULL,0,f,&(id),0,NULL), x != NULL)
#endif
#  define thread_join(x) { WaitForSingleObject(x, INFINITE); CloseHandle(x); }

#endif

#endif // !defined(LOCK_H_INCLUDED)
