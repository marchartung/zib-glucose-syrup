/***************************************************************************************[Main.cc]

 ZIB Glucose -- Copyright (c) 2016 - 2019, Marc Hartung, Zuse Institute Berlin

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose (sources until 2013, Glucose 3.0, single core) are exactly the same as Minisat on which it
is based on. (see below).

Glucose-Syrup sources are based on another copyright. Permissions and copyrights for the parallel
version of Glucose-Syrup (the "Software") are granted, free of charge, to deal with the Software
without restriction, including the rights to use, copy, modify, merge, publish, distribute,
sublicence, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

- The above and below copyrights notices and this permission notice shall be included in all
copies or substantial portions of the Software;
- The parallel version of Glucose (all files modified since Glucose 3.0 releases, 2013) cannot
be used in any competitive event (sat competitions/evaluations) without the express permission of
the authors. This is also the case for any competitive event
using Glucose Parallel as an embedded SAT engine (single core or not).


--------------- Original Minisat Copyrights

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#ifndef PARALLEL_UTILS_LOCKLESSVECTORSTORE_H_
#define PARALLEL_UTILS_LOCKLESSVECTORSTORE_H_

#include "mtl/XAlloc.h"
#include "utils/GarbageCollector.h"

#include <atomic>
#include <algorithm>
#include <tuple>
#include <type_traits>
#include <cstdint>
#include <stdlib.h>
#include "mtl/Vec.h"

namespace Glucose
{

template <typename StoreType, typename AccessType>
struct LockLessVec
{
   LockLessVec() = delete;
   LockLessVec(LockLessVec<StoreType, AccessType> &&) = delete;
   LockLessVec(const LockLessVec<StoreType, AccessType> &) = delete;
   LockLessVec<StoreType, AccessType> & operator=(LockLessVec<StoreType, AccessType> &&) = delete;
   LockLessVec<StoreType, AccessType> & operator=(const LockLessVec<StoreType, AccessType>&) = delete;

   StoreType sz;
   AccessType data[1];

   inline int size() const
   {
      return sz;
   }

   inline const AccessType & operator[](const int idx) const
   {
      return data[idx];
   }

};

template <typename StoreType, typename AccessType>
class LocklessVectorStore
{

   static_assert(sizeof(StoreType) == sizeof(AccessType)
         && sizeof(StoreType) >= sizeof(int)
         && sizeof(std::atomic<StoreType>) == sizeof(AccessType),
         "LocklessVectorStore: Access and StoreType do not fit");
   struct Header
   {
      int sz;
      int cap;

      Header() : sz(0), cap(0) {}

      Header add(const int num)
      {
         Header exp = *this, toBe = exp;

         do
         {
            exp = *this;
            toBe = exp;
            toBe.sz += num;

         } while (!exp.isInvalid() && !atomic().compare_exchange_strong(exp.uint64(), toBe.uint64()));
         // when expectation is already invalid, another thread will allocate more mem

         assert(exp.isInvalid() || sz >= num);
         return exp;
      }

      inline const uint64_t & uint64() const
      {
         return *reinterpret_cast<const uint64_t *>(*this);
      }

      inline uint64_t & uint64()
      {
         return *reinterpret_cast<uint64_t *>(this);
      }

      inline const std::atomic<uint64_t> & atomic() const
      {
         return *reinterpret_cast<const std::atomic<uint64_t> *>(this);
      }

      inline std::atomic<uint64_t> & atomic()
      {
         return *reinterpret_cast<std::atomic<uint64_t> *>(this);
      }

      inline bool isInvalid(const int num = 0) const
      {
         return sz + num > cap;
      }
   };

 public:
   struct Vec
   {
      Header h;
      std::atomic<StoreType> data[1];

      typedef LockLessVec<StoreType, AccessType> VecType;

      const VecType & operator[](const int idx) const
      {
         assert(isValid(idx));
         return *reinterpret_cast<const LockLessVec<StoreType, AccessType>*>(&data[idx]);
      }

      inline bool isValid(const int idx) const
      {
         return idx < h.cap && data[idx] != unvalidMem();
      }

      inline int next(const int pos) const
      {
         return pos + operator[](pos).size() + 1;
      }
   };

   static_assert(sizeof(Header) % sizeof(StoreType) == 0, "VectorOfVectors only allows types with sizes of 4,8 bytes");

   LocklessVectorStore()
         : mem(nullptr)
   {
      assert(mem.is_lock_free());
   }

   LocklessVectorStore(const int defaultSize)
         : LocklessVectorStore()
   {
      grow(defaultSize, nullptr, Header());
   }
   ~LocklessVectorStore()
   {
      free(mem.load());
      mem.store(nullptr);
   }
   inline bool empty() const
   {
      return mem.load() == nullptr;
   }

   inline void * data()
   {
      return mem.load();
   }

   template <typename VecType>
   int push(const VecType & in)
   {
      Header h = reserve(in.size() + 1);
      Vec & v = vec();
      for (int i = 0; i < in.size(); ++i)
      {
         StoreType val = static_cast<StoreType>(in[i]);
         assert(val != unvalidMem());
         v.data[h.sz + 1 + i].store(val, std::memory_order::memory_order_relaxed);
      }
      std::atomic_thread_fence(std::memory_order_release);
      v.data[h.sz].store(in.size());
      return h.sz;
   }

   inline const Vec & vec() const
   {
      return vec(mem.load(std::memory_order::memory_order_acquire));
   }

   void capacity(const int num)
   {
      std::atomic<StoreType> * oldM = mem.load();
      Header h = (oldM != nullptr) ? vec().h : Header( { 0, 0 });
      if (num > h.sz)
         grow(num - h.sz + stdGrow(), oldM, h);
   }

 private:

   static constexpr int stdGrow()
   {
      return 10;
   }
   static constexpr int unvalidMem()
   {
      return std::numeric_limits<int>::max();
   }

   std::atomic<std::atomic<StoreType>*> mem;

   void grow(const int minGrow, std::atomic<StoreType> * oldMem, const Header & oldHeader)
   {
      assert(minGrow > 0);
      if (oldHeader.isInvalid(minGrow))
      {
         int newCap, newMemSize, i = 0;
         std::tie(newCap, newMemSize) = getNewCapacityAndMemorySize(minGrow, oldHeader);
         std::atomic<StoreType> * newMem = static_cast<std::atomic<StoreType>>(aligned_alloc(8,newMemSize));
         Vec * newV = vecP(newMem), *oldV = vecP(mem.load());
         for (; i < oldHeader.sz; ++i)
         {
            while (oldV->data[i].load() == unvalidMem())
               ;  // wait for other threads to finish writing
         }
         memcpy(newV->data, oldV->data, oldHeader.sz * sizeof(StoreType));
         for (; i < newCap; ++i)
            newV->data[i] = unvalidMem();
         newV->h.sz = oldHeader.sz;
         newV->h.cap = newCap;
         if (mem.compare_exchange_strong(oldMem, newMem))
         {
            if (oldMem != nullptr)
            {
               GarbageCollector::threadOwn.add(oldMem);
            }
         } else
         {
            free(newMem);
         }
      }
   }

   std::tuple<int, int> getNewCapacityAndMemorySize(const int minGrow, const Header & h)
   {
      int add = Glucose::vec<int>::imax((minGrow + 1) & ~1, ((h.cap >> 1) + 2) & ~1), newCap = add + h.cap,
            newMemSize = newCap * sizeof(StoreType) + sizeof(Header);

      newMemSize += newMemSize % sizeof(Header);
      newCap = (newMemSize - sizeof(Header)) / sizeof(StoreType);

      return std::make_tuple(newCap, newMemSize);
   }

   Header reserve(const int growBy)
   {
      if (mem.load() == nullptr)
         grow(growBy, nullptr, { 0, 0 });
      std::atomic<StoreType> * cur = mem.load();
      Header res;
      while ((res = vec(cur).h.add(growBy)).isInvalid(growBy))
      {
         if (res.isInvalid())
            while (cur == mem.load(std::memory_order_acquire))
               ;  // wait for other thread to finish grow
         else
            grow(growBy, cur, res);
         cur = mem.load();
      }
      assert(vec(cur).h.sz >= growBy);
      return res;
   }

   inline Vec & vec(std::atomic<StoreType> * val)
   {
      return *reinterpret_cast<Vec*>(val);
   }

   inline const Vec & vec(std::atomic<StoreType> * val) const
   {
      return *reinterpret_cast<const Vec*>(val);
   }
   inline Vec & vec()
   {
      return vec(mem.load(std::memory_order::memory_order_acquire));
   }

   inline Vec * vecP(std::atomic<StoreType> * val)
   {
      return reinterpret_cast<Vec*>(val);
   }
}
;

} /* namespace Concusat */

#endif /* PARALLEL_UTILS_LOCKLESSVECTORSTORE_H_ */
