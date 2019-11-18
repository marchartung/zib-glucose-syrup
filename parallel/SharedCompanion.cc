/***************************************************************************************[SharedCompanion.cc]
 
 Glucose -- Copyright (c) 2009-2017, Gilles Audemard, Laurent Simon
 CRIL - Univ. Artois, France
 LRI  - Univ. Paris Sud, France (2009-2013)
 Labri - Univ. Bordeaux, France
 Glucose -- Copyright (c) 2009-2014, Gilles Audemard, Laurent Simon
 CRIL - Univ. Artois, France
 LRI  - Univ. Paris Sud, France (2009-2013)
 Labri - Univ. Bordeaux, France

 Syrup (Glucose Parallel) -- Copyright (c) 2013-2014, Gilles Audemard, Laurent Simon
 CRIL - Univ. Artois, France
 Labri - Univ. Bordeaux, France

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
 the authors (Gilles Audemard / Laurent Simon). This is also the case for any competitive event
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

#include "core/Solver.h"
#include "parallel/ParallelSolver.h"
#include "core/SolverTypes.h"
#include "parallel/ClausesBuffer.h"
#include "parallel/SharedCompanion.h"

using namespace Glucose;


SharedCompanion::SharedCompanion(const bool & communicateClauses,
		int _nbThreads, int numBuffers) :
		communicate(communicateClauses), nbThreads(_nbThreads), _jobFinishedBy(
				nullptr), panicMode(false), // The bug in the SAT2014 competition :)
		jobStatus(l_Undef), random_seed(9164825), clausesBuffers(numBuffers) {
	pthread_mutex_init(&mutexSharedUnitCompanion, NULL); // This is the shared companion lock
	pthread_mutex_init(&mutexSharedCompanion, NULL); // This is the shared companion lock
	if (_nbThreads > 0) {
		setNbThreadsAndBuffers(_nbThreads, numBuffers);
		fprintf(stdout,
				"c Shared companion initialized: handling of clauses of %d threads.\nc %d ints for the sharing clause buffer (not expandable) .\n",
				_nbThreads, numBuffers);
	}

}

void SharedCompanion::setNbThreadsAndBuffers(int _nbThreads, int numBuffers) {
	nbThreads = _nbThreads;
	if(nextUnit.size() <= _nbThreads)
		nextUnit.growTo(_nbThreads,0);
	if(clausesBuffers.size() <= numBuffers)
	{
		clausesBuffers.growTo(numBuffers);
		//for(unsigned i=clausesBuffers.size();i<numBuffers;++i)
			//clausesBuffers.push(ClausesBuffer(nbThreads,numBuffers));
	}
	for (unsigned i = 0; i < clausesBuffers.size(); ++i)
		clausesBuffers[i].setNbThreads(_nbThreads,numBuffers);
}
unsigned SharedCompanion::getNumBuffers() const
{
	return clausesBuffers.size();
}

unsigned SharedCompanion::getNumThreads() const
{
	return nbThreads;
}

void SharedCompanion::printStats() {
}

void SharedCompanion::newVar(bool sign) {
	isUnary.push(l_Undef);
}

void SharedCompanion::addLearnt(const int & threadId, Lit unary) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	getUnaryLock();
	if (isUnary[var(unary)] == l_Undef) {
		unitLit.push(unary);
		isUnary[var(unary)] = sign(unary) ? l_False : l_True;
	}
	freeUnaryLock();
}

Lit SharedCompanion::getUnary(const int & threadId) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	Lit ret = lit_Undef;
	getUnaryLock();
	if (nextUnit[threadId] < unitLit.size())
		ret = unitLit[nextUnit[threadId]++];
	freeUnaryLock();
	return ret;
}

Lit SharedCompanion::getNoLockUnary(const int & threadId) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	Lit ret = lit_Undef;
	if (nextUnit[threadId] < unitLit.size())
		ret = unitLit[nextUnit[threadId]++];
	return ret;
}

// Specialized functions for this companion
// must be multithread safe
// Add a clause to the threads-wide clause database (all clauses, through)
bool SharedCompanion::addLearnt(const int & threadId, Clause & c, const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	bool ret = false;
	assert(nbThreads > threadId);

	getWriteLock(buffer);
	assert(buffer < clausesBuffers.size());
	ret = clausesBuffers[buffer].pushClause(threadId, c);
	freeWriteLock(buffer);
	return ret;
}

// Specialized functions for this companion
// must be multithread safe
// Add a clause to the threads-wide clause database (all clauses, through)
bool SharedCompanion::addLearntNoLock(const int & threadId, const vec<Lit> & c, const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	bool ret = false;
	assert(nbThreads > threadId);

	assert(buffer < clausesBuffers.size());
	ret = clausesBuffers[buffer].pushClause(threadId, c);
	return ret;
}

void SharedCompanion::getWriteLock(const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	clausesBuffers[buffer].getLock();
}

void SharedCompanion::getReadLock(const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	clausesBuffers[buffer].getLock();
}

void SharedCompanion::freeWriteLock(const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	clausesBuffers[buffer].freeLock();
}

void SharedCompanion::freeReadLock(const unsigned & buffer) {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	clausesBuffers[buffer].freeLock();
}

void SharedCompanion::getUnaryLock() {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	pthread_mutex_lock(&mutexSharedUnitCompanion);
}
void SharedCompanion::freeUnaryLock() {
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	pthread_mutex_unlock(&mutexSharedUnitCompanion);
}

bool SharedCompanion::getNewClause(const int & threadId, int & threadOrigin,
		vec<Lit>& newclause, const unsigned & buffer) { // gets a new interesting clause for solver s
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	// First, let's get the clauses on the big blackboard
	getReadLock(buffer);
	bool b = clausesBuffers[buffer].getClause(threadId, threadOrigin,
			newclause);
	freeReadLock(buffer);
	return b;
}

ParallelSolver * SharedCompanion::jobFinishedBy() {
	return _jobFinishedBy.load();
}

bool SharedCompanion::getNoLockNewClause(const int & threadId, int & threadOrigin,
		vec<Lit>& newclause, const unsigned & buffer) { // gets a new interesting clause for solver s
	assert(
			communicate
					&& "SharedCompanion is called, but communication is disabled.");
	assert(buffer < clausesBuffers.size());
	// First, let's get the clauses on the big blackboard
	bool b = clausesBuffers[buffer].getClause(threadId, threadOrigin, newclause);
	return b;
}

bool SharedCompanion::jobFinished() {
	return _jobFinishedBy.load() != nullptr;
}

bool SharedCompanion::IFinished(ParallelSolver *s) {
	ParallelSolver * exp = nullptr;
	return _jobFinishedBy.compare_exchange_strong(exp, s);
}

