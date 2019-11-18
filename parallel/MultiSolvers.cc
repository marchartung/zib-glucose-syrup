/***************************************************************************************[MultiSolvers.cc]
 
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

#include <pthread.h>
#include "parallel/MultiSolvers.h"
#include "parallel/SharedCompanion.h"
#include "mtl/Sort.h"
#include "utils/System.h"
#include "simp/SimpSolver.h"
#include <errno.h>
#include <string.h>
#include <sched.h>   //cpu_set_t , CPU_SET
#include <pthread.h> //pthread_t
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <stdlib.h>
#include "parallel/SolverConfiguration.h"
#include <iostream>

using namespace Glucose;

extern const char *_parallel;
extern const char *_cunstable;
// Options at the parallel solver level
static IntOption opt_nbsolversmultithreads(_parallel, "nthreads",
		"Number of core threads for syrup (0 for automatic)", 0);
static IntOption opt_maxnbsolvers(_parallel, "maxnbthreads",
		"Maximum number of core threads to ask for (when nbthreads=0)", 4);
static IntOption opt_maxmemory(_parallel, "maxmemory",
		"Maximum memory to use (in Mb, 0 for no software limit)", 20000);
static IntOption opt_statsInterval(_parallel, "statsinterval",
		"Seconds (real time) between two stats reports", 5);

static IntOption opt_numHardwareCores(_parallel, "numcores",
		"Number of physical cores of the system", 2);
static BoolOption opt_coreMappingPacked(_parallel, "corespacked",
		"Determines if the cores should be mapped (if possible) to one socket",
		false);
static BoolOption opt_pinSolvers(_parallel, "pinsolver",
		"Glucose will try to pin the pthreads to a core", false);
static BoolOption opt_communicateClauses(_parallel, "communicateCl",
		"Communicate clauses between solvers", true);
//
// Shared with ClausesBuffer.cc
IntOption opt_numSharedCompanions(_parallel, "numsharecomp",
		"Number of shared companions for clause exchange", 1);
BoolOption opt_whenFullRemoveOlder(_parallel, "removeolder",
		"When the FIFO for exchanging clauses between threads is full, remove older clauses",
		false);
IntOption opt_fifoSizeByCore(_parallel, "fifosize",
		"Size of the FIFO structure for exchanging clauses between threads, by threads",
		100000);
//
// Shared options with Solver.cc 
BoolOption opt_dontExportDirectReusedClauses(_cunstable, "reusedClauses",
		"Don't export directly reused clauses", false);
BoolOption opt_plingeling(_cunstable, "plingeling",
		"plingeling strategy for sharing clauses (exploratory feature)", false);

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

#ifdef __APPLE__

int pthread_barrier_init(pthread_barrier_t *barrier, const pthread_barrierattr_t *attr, unsigned int count)
{
    if(count == 0)
    {
        errno = EINVAL;
        return -1;
    }
    if(pthread_mutex_init(&barrier->mutex, 0) < 0)
    {
        return -1;
    }
    if(pthread_cond_init(&barrier->cond, 0) < 0)
    {
        pthread_mutex_destroy(&barrier->mutex);
        return -1;
    }
    barrier->tripCount = count;
    barrier->count = 0;

    return 0;
}

int pthread_barrier_destroy(pthread_barrier_t *barrier)
{
    pthread_cond_destroy(&barrier->cond);
    pthread_mutex_destroy(&barrier->mutex);
    return 0;
}

int pthread_barrier_wait(pthread_barrier_t *barrier)
{
    pthread_mutex_lock(&barrier->mutex);
    ++(barrier->count);
    if(barrier->count >= barrier->tripCount)
    {
        barrier->count = 0;
        pthread_cond_broadcast(&barrier->cond);
        pthread_mutex_unlock(&barrier->mutex);
        return 1;
    }
    else
    {
        pthread_cond_wait(&barrier->cond, &(barrier->mutex));
        pthread_mutex_unlock(&barrier->mutex);
        return 0;
    }
}

#endif

static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double) ru.ru_utime.tv_sec + (double) ru.ru_utime.tv_usec / 1000000;
}

int cpuMapKnl(int threadId) {
	int res = threadId;
	bool packed = opt_coreMappingPacked;
	int cores = opt_numHardwareCores;
	if (res > cores)
		res = res % cores;

	if (!packed) {
		if (threadId % 2 == 0) {
			if (threadId >= cores / 2) {
				res -= cores / 2;
				res += 1;
			}
		} else {
			if (threadId < cores / 2) {
				res += cores / 2 - 1;
			}
		}
	}
	return res;
}

#define handle_error_en(en, msg) \
               do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

#ifndef __APPLE__
void bindThreadToCpu(int threadId) {
	int cpu = cpuMapKnl(threadId);
	cpu_set_t cpuset;
	CPU_ZERO(&cpuset);       //clears the cpuset
	CPU_SET(cpu, &cpuset); //set CPU 2 on cpuset
	sched_setaffinity(0, sizeof(cpuset), &cpuset);
}

void printCpuBind() {
	cpu_set_t cpuset;
	pthread_t thread = pthread_self();
	int j, s = pthread_getaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
	if (s != 0)
		handle_error_en(s, "pthread_getaffinity_np");

	std::cout << "thread " << pthread_self() << " on cpu ";
	for (j = 0; j < CPU_SETSIZE; j++)
		if (CPU_ISSET(j, &cpuset))
			std::cout << j << " ";
	std::cout << std::endl;
}
#endif

void MultiSolvers::informEnd(lbool res) {
	result = res;
	pthread_cond_broadcast(&cfinished);
}

MultiSolvers::MultiSolvers(ParallelSolver *s) :
		use_simplification(true), ok(true), result(l_Undef), maxnbthreads(4), nbthreads(
				opt_nbsolversmultithreads), nbsolvers(
				opt_nbsolversmultithreads), nbcompanions(4), nbcompbysolver(2), allClonesAreBuilt(
				0), showModel(false), winner(-1), var_decay(1 / 0.95), clause_decay(
				1 / 0.999), cla_inc(1), var_inc(1), random_var_freq(0.02), restart_first(
				100), restart_inc(1.5), learntsize_factor(
				(double) 1 / (double) 3), learntsize_inc(1.1), expensive_ccmin(
				true), polarity_mode(polarity_false), maxmemory(opt_maxmemory), maxnbsolvers(
				opt_maxnbsolvers), verb(0), verbEveryConflicts(10000), numvar(
				0), numclauses(0) {

	sharedcomp = new SharedCompanion(opt_communicateClauses,nbsolvers,opt_numSharedCompanions);
	solvers.push(s);
	initPrimarySolver();
	pthread_mutex_init(&m, NULL);  //PTHREAD_MUTEX_INITIALIZER;
	pthread_mutex_init(&mfinished, NULL); //PTHREAD_MUTEX_INITIALIZER;
	pthread_cond_init(&cfinished, NULL);

}

MultiSolvers::MultiSolvers() :
		MultiSolvers(new ParallelSolver(-1)) {

}

MultiSolvers::~MultiSolvers() {
}

struct SolverCreateConfig {
	int threadId;
	MultiSolvers * ms;
};

void MultiSolvers::initialWait() {
	pthread_barrier_wait(&initBarrier);
}

// TODO: Use a template here
void *MultiSolvers::localLaunch(void *arg) {
	SolverCreateConfig config = *((SolverCreateConfig*) arg);
	if (opt_pinSolvers)
#ifdef __APPLE__
            printf("pinsolver disabled while using Mac OS");
#else
            bindThreadToCpu(config.threadId);
#endif
	ParallelSolver *s;
	if (config.threadId != 0) {
		s = (ParallelSolver *) config.ms->getSolver(0)->clone();
		s->verbosity = 0; // No reportf in solvers... All is done in MultiSolver
		s->setThreadNumber(config.threadId);
		SolverConfiguration::configureCareless(s,config.threadId);
		config.ms->setSolver(config.threadId, s);
	} else
		s = config.ms->getSolver(0);
	config.ms->initialWait();
	(void) s->solve();
	pthread_exit(NULL);
}

Var MultiSolvers::newVar(bool sign, bool dvar) {
	assert(solvers[0] != NULL);
	numvar++;
	int v;
	sharedcomp->newVar(sign);
	if (!allClonesAreBuilt) { // At the beginning we want to generate only solvers 0
		v = solvers[0]->newVar(sign, dvar);
		assert(numvar == v + 1); // Just a useless check
	} else {
		for (int i = 0; i < nbsolvers; i++) {
			v = solvers[i]->newVar(sign, dvar);
		}
	}
	return numvar;
}

bool MultiSolvers::addClause_(vec<Lit> &ps) {
	assert(solvers[0] != NULL); // There is at least one solver.
	// Check if clause is satisfied and remove false/duplicate literals:
	if (!okay())
		return false;

	sort(ps);
	Lit p;
	int i, j;
	for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
		if (solvers[0]->value(ps[i]) == l_True || ps[i] == ~p)
			return true;
		else if (solvers[0]->value(ps[i]) != l_False && ps[i] != p)
			ps[j++] = p = ps[i];
	ps.shrink(i - j);

	if (ps.size() == 0) {
		return ok = false;
	} else if (ps.size() == 1) {
		assert(solvers[0]->value(ps[0]) == l_Undef); // TODO : Passes values to all threads
		solvers[0]->uncheckedEnqueue(ps[0]);
		if (!allClonesAreBuilt) {
			return ok = ((solvers[0]->propagate()) == CRef_Undef); // checks only main solver here for propagation constradiction
		}

		// Here, all clones are built.
		// Gives the unit clause to everybody
		for (int i = 0; i < nbsolvers; i++)
			solvers[i]->uncheckedEnqueue(ps[0]);
		return ok = ((solvers[0]->propagate()) == CRef_Undef); // checks only main solver here for propagation constradiction
	} else {
		//		printf("Adding clause %0xd for solver %d.\n",(void*)c, thn);
		// At the beginning only solver 0 load the formula
		solvers[0]->addClause(ps);

		if (!allClonesAreBuilt) {
			numclauses++;
			return true;
		}
		// Clones are built, need to pass the clause to all the threads
		for (int i = 1; i < nbsolvers; i++) {
			solvers[i]->addClause(ps);
		}
		numclauses++;
	}
	return true;
}

bool MultiSolvers::simplify() {
	assert(solvers[0] != NULL); // There is at least one solver.

	if (!okay())
		return false;
	return ok = solvers[0]->simplify();
}

bool MultiSolvers::eliminate() {

	// TODO allow variable elimination when all threads are built!
	assert(allClonesAreBuilt == false);

	SimpSolver *s = (SimpSolver *) getPrimarySolver();
	s->use_simplification = use_simplification;
	if (!use_simplification)
		return true;

	return s->eliminate(true);
}

void MultiSolvers::printStats() {
	static int nbprinted = 1;
	double cpu_time = cpuTime();
	printf("c\n");

	printf(
			"c |-------------------------------------------------------------------------------------------------------|\n");
	printf(
			"c | id | starts | decisions  |  confls    |  Init T  |  learnts | exported | imported | promoted |    %%   | \n");
	printf(
			"c |-------------------------------------------------------------------------------------------------------|\n");

	//printf("%.0fs | ",cpu_time);
	for (int i = 0; i < solvers.size(); i++) {
		solvers[i]->reportProgress();
		//printf(" %2d: %12ld confl. |", i,  (long int) solvers[i]->conflicts);
	}
	long long int totalconf = 0;
	long long int totalprop = 0;
	for (int i = 0; i < solvers.size(); i++) {
		totalconf += (long int) solvers[i]->conflicts;
		totalprop += solvers[i]->propagations;
	}
	printf("c \n");

	printf(
			"c synthesis %11lld conflicts %11lld propagations %8.0f conflicts/sec %8.0f propagations/sec\n",
			totalconf, totalprop, (double) totalconf / cpu_time,
			(double) totalprop / cpu_time);

	nbprinted++;
}

// Still a ugly function... To be rewritten with some statistics class some day
void MultiSolvers::printFinalStats() {
	sharedcomp->printStats();
	printf("c\nc\n");
	printf("c\n");
	printf(
			"c |---------------------------------------- FINAL STATS --------------------------------------------------|\n");
	printf("c\n");

	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

	printf("c | Threads       |      Total      ");
	for (int i = 0; i < solvers.size(); i++) {
		printf("| %10d ", i);
	}
	printf("|\n");

	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

//--
	printf("c | Conflicts     ");
	long long int totalconf = 0;
	for (int i = 0; i < solvers.size(); i++)
		totalconf += solvers[i]->conflicts;
	printf("| %15lld ", totalconf);

	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->conflicts);
	printf("|\n");

	//--
	printf("c | Decisions     ");
	long long int totaldecs = 0;
	for (int i = 0; i < solvers.size(); i++)
		totaldecs += solvers[i]->decisions;
	printf("| %15lld ", totaldecs);

	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->decisions);
	printf("|\n");

	//--
	printf("c | Propagations  ");
	long long int totalprops = 0;
	for (int i = 0; i < solvers.size(); i++)
		totalprops += solvers[i]->propagations;
	printf("| %15lld ", totalprops);

	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->propagations);
	printf("|\n");

	printf("c | Avg_Trail     ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->conflicts == 0 ?
						0 :
						solvers[i]->stats[sumTrail] / solvers[i]->conflicts);
	printf("|\n");

	//--
	printf("c | Avg_DL        ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->conflicts == 0 ?
						0 :
						solvers[i]->stats[sumDecisionLevels]
								/ solvers[i]->conflicts);
	printf("|\n");

	//--
	printf("c | Avg_Res       ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->conflicts == 0 ?
						0 : solvers[i]->stats[sumRes] / solvers[i]->conflicts);
	printf("|\n");

	//--
	printf("c | Avg_Res_Seen  ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->conflicts == 0 ?
						0 :
						solvers[i]->stats[sumResSeen] / solvers[i]->conflicts);
	printf("|\n");

	//--

	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

	printf("c | Exported      ");
	uint64_t exported = 0;
	for (int i = 0; i < solvers.size(); i++)
		exported += solvers[i]->stats[nbexported];
	printf("| %15" PRIu64" ", exported);

	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->stats[nbexported]);
	printf("|\n");
//--    
	printf("c | Imported      ");
	uint64_t imported = 0;
	for (int i = 0; i < solvers.size(); i++)
		imported += solvers[i]->stats[nbimported];
	printf("| %15" PRIu64" ", imported);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->stats[nbimported]);
	printf("|\n");
//--

	printf("c | Good          ");
	uint64_t importedGood = 0;
	for (int i = 0; i < solvers.size(); i++)
		importedGood += solvers[i]->stats[nbImportedGoodClauses];
	printf("| %15" PRIu64" ", importedGood);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->stats[nbImportedGoodClauses]);
	printf("|\n");
//--

	printf("c | Purge         ");
	uint64_t importedPurg = 0;
	for (int i = 0; i < solvers.size(); i++)
		importedPurg += solvers[i]->stats[nbimportedInPurgatory];
	printf("| %15" PRIu64" ", importedPurg);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->stats[nbimportedInPurgatory]);
	printf("|\n");
//-- 

	printf("c | Promoted      ");
	uint64_t promoted = 0;
	for (int i = 0; i < solvers.size(); i++)
		promoted += solvers[i]->stats[nbPromoted];
	printf("| %15" PRIu64" ", promoted);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ", solvers[i]->stats[nbPromoted]);
	printf("|\n");
//--

	printf("c | Remove_Imp    ");
	uint64_t removedimported = 0;
	for (int i = 0; i < solvers.size(); i++)
		removedimported += solvers[i]->stats[nbRemovedUnaryWatchedClauses];
	printf("| %15" PRIu64" ", removedimported);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->stats[nbRemovedUnaryWatchedClauses]);
	printf("|\n");
//--

	printf("c | Blocked_Reuse ");
	uint64_t blockedreused = 0;
	for (int i = 0; i < solvers.size(); i++)
		blockedreused += solvers[i]->nbNotExportedBecauseDirectlyReused;
	printf("| %15" PRIu64" ", blockedreused);
	for (int i = 0; i < solvers.size(); i++)
		printf("| %10" PRIu64" ",
				solvers[i]->nbNotExportedBecauseDirectlyReused);
	printf("|\n");
//--
	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

	printf("c | Unaries       ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++) {
		printf("| %10" PRIu64" ", solvers[i]->stats[nbUn]);
	}
	printf("|\n");
//--

	printf("c | Binaries      ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++) {
		printf("| %10" PRIu64" ", solvers[i]->stats[nbBin]);
	}
	printf("|\n");
//--

	printf("c | Glues         ");
	printf("|                 ");
	for (int i = 0; i < solvers.size(); i++) {
		printf("| %10" PRIu64" ", solvers[i]->stats[nbDL2]);
	}
	printf("|\n");
//--

	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

	printf("c | Orig_Seen     ");
	uint64_t origseen = 0;

	for (int i = 0; i < solvers.size(); i++) {
		origseen += solvers[i]->stats[originalClausesSeen];
	}
	printf("| %13" PRIu64" %% ", origseen * 100 / nClauses() / solvers.size());

	for (int i = 0; i < solvers.size(); i++) {
		printf("| %10" PRIu64" ", solvers[i]->stats[originalClausesSeen]);
	}

	printf("|\n");

	int winner = -1;
	for (int i = 0; i < solvers.size(); i++) {
		if (sharedcomp->winner() == solvers[i])
			winner = i;
	}

//--
	if (winner != -1) {
		printf("c | Diff Orig seen");
		printf("|                 ");

		for (int i = 0; i < solvers.size(); i++) {
			if (i == winner) {
				printf("|      X     ");
				continue;
			}
			if (solvers[i]->stats[originalClausesSeen]
					> solvers[winner]->stats[originalClausesSeen])
				printf("| %10" PRIu64" ",
						solvers[i]->stats[originalClausesSeen]
								- solvers[winner]->stats[originalClausesSeen]);
			else
				printf("| -%9" PRIu64" ",
						solvers[winner]->stats[originalClausesSeen]
								- solvers[i]->stats[originalClausesSeen]);

		}

		printf("|\n");
	}

//--

	if (winner != -1) {
		int sum = 0;
		printf("c | Hamming       ");
		for (int i = 0; i < solvers.size(); i++) {
			if (i == winner)
				continue;
			int nb = 0;
			for (int j = 0; j < nVars(); j++) {
				if (solvers[i]->valuePhase(j) != solvers[winner]->valuePhase(j))
					nb++;
			}
			sum += nb;

		}
		sum = sum / (solvers.size() > 1 ? solvers.size() - 1 : 1);

		printf("| %13d %% ", sum * 100 / nVars());

		for (int i = 0; i < solvers.size(); i++) {
			if (i == winner) {
				printf("|      X     ");
				continue;
			}
			int nb = 0;
			for (int j = 0; j < nVars(); j++) {
				if (solvers[i]->valuePhase(j) != solvers[winner]->valuePhase(j))
					nb++;
			}
			printf("| %10d ", nb);
			sum += nb;

		}
		printf("|\n");
	}

	printf("c |---------------|-----------------");
	for (int i = 0; i < solvers.size(); i++)
		printf("|------------");
	printf("|\n");

}

void MultiSolvers::adjustNumberOfCores() {
	float mem = memUsed();
	if (nbthreads == 0) { // Automatic configuration
		if (verb >= 1)
			printf(
					"c |  Automatic Adjustement of the number of solvers. MaxMemory=%5d, MaxCores=%3d.                       |\n",
					maxmemory, maxnbsolvers);
		unsigned int tmpnbsolvers = maxmemory * 4 / 10 / mem;
		if (tmpnbsolvers > maxnbsolvers)
			tmpnbsolvers = maxnbsolvers;
		if (tmpnbsolvers < 1)
			tmpnbsolvers = 1;
		if (verb >= 1)
			printf(
					"c |  One Solver is taking %.2fMb... Let's take %d solvers for this run (max 40%% of the maxmemory).       |\n",
					mem, tmpnbsolvers);
		nbsolvers = tmpnbsolvers;
		nbthreads = nbsolvers;
	} else {
		assert(nbthreads == nbsolvers);
	}
}

void MultiSolvers::initPrimarySolver() {

	// Generate only solver 0.
	// It loads the formula
	// All others solvers are clone of this one
	assert(solvers.size() == 1);
	ParallelSolver *s = solvers[0];
	s->verbosity = 0; // No reportf in solvers... All is done in MultiSolver
	s->setThreadNumber(0);
	//s->belongsto = this;
	s->sharedcomp = this->sharedcomp;
	assert(solvers[0]->threadNumber() == 0);

	s->pmfinished = &mfinished;
	s->pcfinished = &cfinished;

	if (nbsolvers > 0)
		fprintf(stdout,
				"c %d solvers engines and %d companion as a blackboard created.\n",
				nbsolvers, this->sharedcomp->clausesBuffers.size());
	SolverConfiguration::configureCareless(s,0);
}

void MultiSolvers::initSolvers() {
	pthread_attr_t thAttr;
	int i;

	if (verb >= 1)
		printf(
				"c |  Generating clones                                                                                    |\n");

	model.clear();

	/* Initialize and set thread detached attribute */
	pthread_attr_init(&thAttr);
	pthread_attr_setdetachstate(&thAttr, PTHREAD_CREATE_JOINABLE);

	pthread_barrier_init(&initBarrier, NULL, nbsolvers + 1);
	SolverCreateConfig threadConfigs[nbsolvers];
	solvers.growTo(nbsolvers);
	// Launching all solvers
	for (i = 0; i < nbsolvers; i++) {
		pthread_t *pt = (pthread_t *) malloc(sizeof(pthread_t));
		threads.push(pt);
		threadConfigs[i].threadId = i;
		threadConfigs[i].ms = this;
		pthread_create(threads[i], &thAttr, &localLaunch, &threadConfigs[i]);
	}
	initialWait();
	if (verb >= 1) {
		printf(
				"c |  all clones generated. Memory = %6.2fMb.                                                             |\n",
				memUsed());
		printf(
				"c ========================================================================================================|\n");
	}
	allClonesAreBuilt = 1;
}

void MultiSolvers::printAndAdjust(const bool & done, bool & adjustedlimitonce) {
	float mem = memUsed();
	if (verb >= 1)
		printf("c Total Memory so far : %.2fMb\n", mem);
	if ((maxmemory > 0) && (mem > maxmemory) && !sharedcomp->panicMode)
		printf(
				"c ** reduceDB switching to Panic Mode due to memory limitations !\n"), sharedcomp->panicMode =
				true;

	if (!done && !adjustedlimitonce) {
		uint64_t sumconf = 0;
		uint64_t sumimported = 0;
		for (int i = 0; i < nbsolvers; i++) {
			sumconf += solvers[i]->conflicts;
			sumimported += solvers[i]->stats[nbimported];
		}
		if (sumconf > 10000000 && sumimported > 4 * sumconf) { // too many many imported clauses (after a while)
			for (int i = 0; i < nbsolvers; i++) { // we have like 32 threads, so we need to export just very good clauses
				solvers[i]->goodlimitlbd -= 2;
				solvers[i]->goodlimitsize -= 4;
			}
			adjustedlimitonce = true;
			printf("c adjusting (once) the limits to send fewer clauses.\n");
		}
	}
}

void MultiSolvers::joinSolvers()
{
	//printf("Main thread unlocks\n");

	//printf("Main thread joins\n");
	for (unsigned i = 0; i < nbsolvers; i++) { // Wait for all threads to finish
		pthread_join(*threads[i], NULL);
		//	printf("Main thread joins with %d\n",i);
	}
	//printf("Main thread finished joining\n");
}

void MultiSolvers::setResult()
{
	assert(sharedcomp != NULL);
	result = sharedcomp->jobStatus;
	if (result == l_True) {
		sharedcomp->jobFinishedBy()->extendModel();
		int n = sharedcomp->jobFinishedBy()->nVars();
		model.growTo(n);
		for (int i = 0; i < n; i++) {
			model[i] = sharedcomp->jobFinishedBy()->model[i];
			assert(model[i] != l_Undef);
		}
	}
}
lbool MultiSolvers::solve() {
	initSolvers();

	bool done = false;
	bool adjustedlimitonce = false;

	pthread_mutex_lock(&m);
	while (!done) {
		struct timespec timeout;
		time(&timeout.tv_sec);
		timeout.tv_sec += MAXIMUM_SLEEP_DURATION;
		timeout.tv_nsec = 0;
		if (pthread_cond_timedwait(&cfinished, &mfinished,
				&timeout) != ETIMEDOUT) {
			done = true;
		} else
			printStats();
		printAndAdjust(done,adjustedlimitonce);
	}


	pthread_mutex_unlock(&m);
	joinSolvers();
	setResult();
	return result;

}
