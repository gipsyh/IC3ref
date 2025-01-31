/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <algorithm>
#include <iostream>
#include <set>
#include <sys/times.h>
#include <signal.h>

#include "IC3.h"
#include "Solver.h"
#include "Vec.h"
#include "transys.h"
#include "gipsat.h"

// A reference implementation of IC3, i.e., one that is meant to be
// read and used as a starting point for tuning, extending, and
// experimenting.
//
// High-level details:
//
//  o The overall structure described in
//
//      Aaron R. Bradley, "SAT-Based Model Checking without
//      Unrolling," VMCAI'11
//
//    including frames, a priority queue of frame-specific proof
//    obligations, and induction-based generalization.  See check(),
//    strengthen(), handleObligations(), mic(), propagate().
//
//  o Lifting, inspired by
//
//      Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient
//      Implementation of Property Directed Reachability," FMCAD'11
//
//    Each CTI is lifted to a larger cube whose states all have the
//    same successor.  The implementation is based on
//
//      H. Chockler, A. Ivrii, A. Matsliah, S. Moran, and Z. Nevo,
//      "Incremental Formal Veriﬁcation of Hardware," FMCAD'11.
//
//    In particular, if s with inputs i is a predecessor of t, then s
//    & i & T & ~t' is unsatisfiable, where T is the transition
//    relation.  The unsat core reveals a suitable lifting of s.  See
//    stateOf().
//
//  o One solver per frame, which various authors of IC3
//    implementations have tried (including me in pre-publication
//    work, at which time I thought that moving to one solver was
//    better).
//
//  o A straightforward proof obligation scheme, inspired by the ABC
//    implementation.  I have so far favored generalizing relative to
//    the maximum possible level in order to avoid over-strengthening,
//    but doing so requires a more complicated generalization scheme.
//    Experiments by Zyad Hassan indicate that generalizing relative
//    to earlier levels works about as well.  Because literals seem to
//    be dropped more quickly, an implementation of the "up" algorithm
//    (described in my FMCAD'07 paper) is unnecessary.
//
//    The scheme is as follows.  For obligation <s, i>:
//
//    1. Check consecution of ~s relative to i-1.
//
//    2. If it succeeds, generalize, then push foward to, say, j.  If
//       j <= k (the frontier), enqueue obligation <s, j>.
//
//    3. If it fails, extract the predecessor t (using stateOf()) and
//       enqueue obligation <t, i-1>.
//
//    The upshot for this reference implementation is that it is
//    short, simple, and effective.  See handleObligations() and
//    generalize().
//
//  o The generalization method described in
//
//      Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//      Generalization in IC3," (submitted May 2013)
//
//    which seems to be superior to the single-clause method described
//    in the original paper, first described in
//
//      Aaron R. Bradley and Zohar Manna, "Checking Safety by
//      Inductive Generalization of Counterexamples to Induction,"
//      FMCAD'07
//
//    The main idea is to address not only CTIs, which are states
//    discovered through IC3's explict backward search, but also
//    counterexamples to generalization (CTGs), which are states that
//    are counterexamples to induction during generalization.  See
//    mic() and ctgDown().
//
//    A basic one-cube generalization scheme can be used instead
//    (third argument of check()).
//
// Limitations in roughly descending order of significance:
//
//  o A permanent limitation is that there is absolutely no
//    simplification of the AIGER spec.  Use, e.g.,
//
//      iimc -t pp -t print_aiger
//
//    or ABC's simplification methods to produce preprocessed AIGER
//    benchmarks.  This implementation is intentionally being kept
//    small and simple.
//
//  o An implementation of "up" is not provided, as it seems that it's
//    unnecessary when both lifting-based and unsat core-based
//    reduction are applied to a state, followed by mic before
//    pushing.  The resulting cube is sufficiently small.

namespace IC3
{

GipSAT *glabol_gipsat;

class IC3 {
    public:
	IC3(Transys &_model)
		: verbose(0)
		, random(false)
		, model(_model)
		, nextState(0)
		, litOrder()
		, slimLitOrder()
		, numLits(0)
		, numUpdates(0)
		, maxDepth(1)
		, maxCTGs(3)
		, maxJoins(1 << 20)
		, micAttempts(3)
		, cexState(0)
		, nQuery(0)
		, nCTI(0)
		, nCTG(0)
		, nmic(0)
		, satTime(0)
		, nCoreReduced(0)
		, nAbortJoin(0)
		, nAbortMic(0)
	{
		slimLitOrder.heuristicLitOrder = &litOrder;
		gipsat = new GipSAT(model);
		glabol_gipsat = gipsat;
		gipsat->extend();
	}
	~IC3()
	{
		delete gipsat;
	}

	// The main loop.
	bool check()
	{
		startTime = time(); // stats
		extend();
		while (true) {
			if (!strengthen())
				return false;
			extend();
			if (propagate())
				return true;
			printStats();
		}
	}

    private:
	int verbose; // 0: silent, 1: stats, 2: all
	bool random;

	Transys &model;

	// The State structures are for tracking trees of (lifted) CTIs.
	// Because States are created frequently, I want to avoid dynamic
	// memory management; instead their (de)allocation is handled via
	// a vector-based pool.
	struct State {
		size_t successor; // successor State
		LitVec latches;
		LitVec inputs;
		size_t index; // for pool
		bool used; // for pool
	};
	vector<State> states;
	size_t nextState;
	// WARNING: do not keep reference across newState() calls
	State &state(size_t sti)
	{
		return states[sti - 1];
	}
	size_t newState()
	{
		if (nextState >= states.size()) {
			states.resize(states.size() + 1);
			states.back().index = states.size();
			states.back().used = false;
		}
		size_t ns = nextState;
		assert(!states[ns].used);
		states[ns].used = true;
		while (nextState < states.size() && states[nextState].used)
			nextState++;
		return ns + 1;
	}
	void delState(size_t sti)
	{
		State &st = state(sti);
		st.used = false;
		st.latches.clear();
		st.inputs.clear();
		if (nextState > st.index - 1)
			nextState = st.index - 1;
	}
	void resetStates()
	{
		for (vector<State>::iterator i = states.begin(); i != states.end(); ++i) {
			i->used = false;
			i->latches.clear();
			i->inputs.clear();
		}
		nextState = 0;
	}

	// A CubeSet is a set of ordered (by integer value) vectors of
	// Minisat::Lits.
	static bool _LitVecComp(const LitVec &v1, const LitVec &v2)
	{
		if (v1.size() < v2.size())
			return true;
		if (v1.size() > v2.size())
			return false;
		for (size_t i = 0; i < v1.size(); ++i) {
			if (v1[i] < v2[i])
				return true;
			if (v2[i] < v1[i])
				return false;
		}
		return false;
	}
	static bool _LitVecEq(const LitVec &v1, const LitVec &v2)
	{
		if (v1.size() != v2.size())
			return false;
		for (size_t i = 0; i < v1.size(); ++i)
			if (v1[i] != v2[i])
				return false;
		return true;
	}
	class LitVecComp {
	    public:
		bool operator()(const LitVec &v1, const LitVec &v2)
		{
			return _LitVecComp(v1, v2);
		}
	};
	typedef set<LitVec, LitVecComp> CubeSet;

	// A proof obligation.
	struct Obligation {
		Obligation(size_t st, size_t l, size_t d)
			: state(st)
			, level(l)
			, depth(d)
		{
		}
		size_t state; // Generalize this state...
		size_t level; // ... relative to this level.
		size_t depth; // Length of CTI suffix to error.
	};
	class ObligationComp {
	    public:
		bool operator()(const Obligation &o1, const Obligation &o2)
		{
			if (o1.level < o2.level)
				return true; // prefer lower levels (required)
			if (o1.level > o2.level)
				return false;
			if (o1.depth < o2.depth)
				return true; // prefer shallower (heuristic)
			if (o1.depth > o2.depth)
				return false;
			if (o1.state < o2.state)
				return true; // canonical final decider
			return false;
		}
	};
	typedef set<Obligation, ObligationComp> PriorityQueue;

	struct Frame {
		size_t k; // steps from initial state
		CubeSet borderCubes; // additional cubes in this and previous frames
		GipSAT *consecution;
	};
	vector<Frame> frames;
	
	Minisat::Solver *lifts;
	void extend()
	{
		while (frames.size() < k + 2) {
			frames.resize(frames.size() + 1);
			Frame &fr = frames.back();
			fr.k = frames.size() - 1;
			fr.consecution = new GipSAT(model);
			if (random) {
				fr.consecution->random_seed = rand();
				fr.consecution->rnd_init_act = true;
			}
			if (fr.k == 0)
				model.loadInitialCondition(*fr.consecution);
			model.loadTransitionRelation(*fr.consecution);
		}
	}

	struct HeuristicLitOrder {
		HeuristicLitOrder()
			: _mini(1 << 20)
		{
		}
		vector<float> counts;
		size_t _mini;
		void count(const LitVec &cube)
		{
			assert(!cube.empty());
			// assumes cube is ordered
			size_t sz = (size_t)Minisat::toInt(Minisat::var(cube.back()));
			if (sz >= counts.size())
				counts.resize(sz + 1);
			_mini = (size_t)Minisat::toInt(Minisat::var(cube[0]));
			for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
				counts[(size_t)Minisat::toInt(Minisat::var(*i))] += 1;
		}
		void decay()
		{
			for (size_t i = _mini; i < counts.size(); ++i)
				counts[i] *= 0.99;
		}
	} litOrder;

	struct SlimLitOrder {
		HeuristicLitOrder *heuristicLitOrder;

		SlimLitOrder()
		{
		}

		bool operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const
		{
			// l1, l2 must be unprimed
			size_t i2 = (size_t)Minisat::toInt(Minisat::var(l2));
			if (i2 >= heuristicLitOrder->counts.size())
				return false;
			size_t i1 = (size_t)Minisat::toInt(Minisat::var(l1));
			if (i1 >= heuristicLitOrder->counts.size())
				return true;
			return (heuristicLitOrder->counts[i1] < heuristicLitOrder->counts[i2]);
		}
	} slimLitOrder;

	float numLits, numUpdates;
	void updateLitOrder(const LitVec &cube, size_t level)
	{
		litOrder.decay();
		numUpdates += 1;
		numLits += cube.size();
		litOrder.count(cube);
	}

	// order according to preference
	void orderCube(LitVec &cube)
	{
		stable_sort(cube.begin(), cube.end(), slimLitOrder);
	}

	typedef Minisat::vec<Minisat::Lit> MSLitVec;

	// Orders assumptions for Minisat.
	void orderAssumps(LitVec &cube, bool rev, int start = 0)
	{
		stable_sort(cube.begin() + start, cube.begin() + cube.size(), slimLitOrder);
		if (rev)
			reverse(cube.begin() + start, cube.begin() + cube.size());
	}

	size_t stateOf(size_t succ = 0)
	{
		size_t st = newState();
		state(st).successor = succ;
		++nQuery;
		startTimer();
		vector<uint> p = gipsat->get_predecessor();
		for (auto l : p) {
			state(st).latches.push_back(Minisat::Lit{ l });
		}
		endTimer(satTime);
		return st;
	}

	// Checks if cube contains any initial states.
	bool initiation(const LitVec &latches)
	{
		return !model.cube_subsume_init((vector<uint> &)latches);
	}

	bool consecution(size_t fi, const LitVec &latches, size_t succ = 0, LitVec *core = NULL, size_t *pred = NULL,
			 bool orderedCore = false)
	{
		LitVec assumps = latches;
		if (pred)
			orderAssumps(assumps, false);
		else
			orderAssumps(assumps, orderedCore);
		++nQuery;
		startTimer(); // stats
		bool rv = gipsat->inductive(fi + 1, (vector<uint> &)assumps, true);
		endTimer(satTime);
		if (!rv) {
			if (pred)
				*pred = stateOf(succ);
			return false;
		}
		if (core) {
			if (pred && orderedCore) {
				reverse(assumps.begin(), assumps.begin() + assumps.size());
				++nQuery;
				startTimer(); // stats
				rv = gipsat->inductive(fi + 1, (vector<uint> &)assumps, true);
				assert(rv);
				endTimer(satTime);
			}
			vector<uint> c = gipsat->inductive_core();
			*core = LitVec();
			for (auto l : c) {
				core->push_back(Minisat::Lit{ l });
			}
		}
		return true;
	}

	size_t maxDepth, maxCTGs, maxJoins, micAttempts;

	// Based on
	//
	//   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
	//   Generalization in IC3," (submitted May 2013)
	//
	// Improves upon "down" from the original paper (and the FMCAD'07
	// paper) by handling CTGs.
	bool ctgDown(size_t level, LitVec &cube, size_t keepTo, size_t recDepth)
	{
		size_t ctgs = 0, joins = 0;
		while (true) {
			// induction check
			if (!initiation(cube))
				return false;
			if (recDepth > maxDepth) {
				// quick check if recursion depth is exceeded
				LitVec core;
				bool rv = consecution(level, cube, 0, &core, NULL, true);
				if (rv && core.size() < cube.size()) {
					++nCoreReduced; // stats
					cube = core;
				}
				return rv;
			}
			abort();
			// prepare to obtain CTG
			size_t cubeState = newState();
			state(cubeState).successor = 0;
			state(cubeState).latches = cube;
			size_t ctg;
			LitVec core;
			if (consecution(level, cube, cubeState, &core, &ctg, true)) {
				if (core.size() < cube.size()) {
					++nCoreReduced; // stats
					cube = core;
				}
				// inductive, so clean up
				delState(cubeState);
				return true;
			}
			// not inductive, address interfering CTG
			LitVec ctgCore;
			bool ret = false;
			if (ctgs < maxCTGs && level > 1 && initiation(state(ctg).latches) &&
			    consecution(level - 1, state(ctg).latches, cubeState, &ctgCore)) {
				// CTG is inductive relative to level-1; push forward and generalize
				++nCTG; // stats
				++ctgs;
				size_t j = level;
				// QUERY: generalize then push or vice versa?
				while (j < gipsat->level() && consecution(j, ctgCore))
					++j;
				mic(j - 1, ctgCore, recDepth + 1);
				addCube(j, ctgCore);
			} else if (joins < maxJoins) {
				// ran out of CTG attempts, so join instead
				ctgs = 0;
				++joins;
				LitVec tmp;
				for (size_t i = 0; i < cube.size(); ++i)
					if (binary_search(state(ctg).latches.begin(), state(ctg).latches.end(),
							  cube[i]))
						tmp.push_back(cube[i]);
					else if (i < keepTo) {
						// previously failed when this literal was dropped
						++nAbortJoin; // stats
						ret = true;
						break;
					}
				cube = tmp; // enlarged cube
			} else
				ret = true;
			// clean up
			delState(cubeState);
			delState(ctg);
			if (ret)
				return false;
		}
	}

	// Extracts minimal inductive (relative to level) subclause from
	// ~cube --- at least that's where the name comes from.  With
	// ctgDown, it's not quite a MIC anymore, but what's returned is
	// inductive relative to the possibly modifed level.
	void mic(size_t level, LitVec &cube, size_t recDepth)
	{
		++nmic; // stats
		// try dropping each literal in turn
		size_t attempts = micAttempts;
		vector<uint> domain;
		for (auto l : cube) {
			domain.push_back(l.x);
			domain.push_back(model.lit_next(l.x));
		}
		gipsat->set_domain(level, domain);
		orderCube(cube);
		for (size_t i = 0; i < cube.size();) {
			LitVec cp(cube.begin(), cube.begin() + i);
			cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
			if (ctgDown(level, cp, i, recDepth)) {
				// maintain original order
				LitSet lits(cp.begin(), cp.end());
				LitVec tmp;
				for (LitVec::const_iterator j = cube.begin(); j != cube.end(); ++j)
					if (lits.find(*j) != lits.end())
						tmp.push_back(*j);
				cube.swap(tmp);

				gipsat->unset_domain(level);
				vector<uint> domain;
				for (auto l : cube) {
					domain.push_back(l.x);
					domain.push_back(model.lit_next(l.x));
				}
				gipsat->set_domain(level, domain);
				// reset attempts
				attempts = micAttempts;
			} else {
				if (!--attempts) {
					// Limit number of attempts: if micAttempts literals in a
					// row cannot be dropped, conclude that the cube is just
					// about minimal.  Definitely improves mics/second to use
					// a low micAttempts, but does it improve overall
					// performance?
					++nAbortMic; // stats
					gipsat->unset_domain(level);
					return;
				}
				++i;
			}
		}
		gipsat->unset_domain(level);
	}

	// wrapper to start inductive generalization
	void mic(size_t level, LitVec &cube)
	{
		mic(level, cube, 1);
	}

	void addCube(size_t level, LitVec &cube)
	{
		gipsat->add_lemma(level, (vector<uint> &)cube);
	}

	// ~cube was found to be inductive relative to level; now see if
	// we can do better.
	size_t generalize(size_t level, LitVec cube)
	{
		// generalize
		mic(level, cube);
		// push
		do {
			++level;
		} while (level < gipsat->level() && consecution(level, cube));
		addCube(level, cube);
		return level;
	}

	size_t cexState; // beginning of counterexample trace

	// Process obligations according to priority.
	bool handleObligations(PriorityQueue obls)
	{
		while (!obls.empty()) {
			PriorityQueue::iterator obli = obls.begin();
			Obligation obl = *obli;
			LitVec core;
			size_t predi;
			// Is the obligation fulfilled?
			if (consecution(obl.level, state(obl.state).latches, obl.state, &core, &predi)) {
				// Yes, so generalize and possibly produce a new obligation
				// at a higher level.
				obls.erase(obli);
				size_t n = generalize(obl.level, core);
				if (n < gipsat->level())
					obls.insert(Obligation(obl.state, n, obl.depth));
			} else if (obl.level == 0) {
				// No, in fact an initial state is a predecessor.
				cexState = predi;
				return false;
			} else {
				++nCTI; // stats
				// No, so focus on predecessor.
				obls.insert(Obligation(predi, obl.level - 1, obl.depth + 1));
			}
		}
		return true;
	}

	bool strengthen()
	{
		while (true) {
			++nQuery;
			startTimer(); // stats
			bool rv = gipsat->has_bad();
			endTimer(satTime);
			if (!rv)
				return true;
			// handle CTI with error successor
			++nCTI; // stats
			PriorityQueue pq;
			// enqueue main obligation and handle
			pq.insert(Obligation(stateOf(), gipsat->level() - 1, 1));
			if (!handleObligations(pq))
				return false;
			// finished with States for this iteration, so clean up
			resetStates();
		}
	}

	bool propagate()
	{
		return gipsat->propagate();
	}

	int nQuery, nCTI, nCTG, nmic;
	clock_t startTime, satTime;
	int nCoreReduced, nAbortJoin, nAbortMic;
	clock_t time()
	{
		struct tms t;
		times(&t);
		return t.tms_utime;
	}
	clock_t timer;
	void startTimer()
	{
		timer = time();
	}
	void endTimer(clock_t &t)
	{
		t += (time() - timer);
	}
	void printStats()
	{
		if (!verbose)
			return;
		clock_t etime = time();
		cout << ". Elapsed time: " << ((double)etime / sysconf(_SC_CLK_TCK)) << endl;
		etime -= startTime;
		if (!etime)
			etime = 1;
		cout << ". % SAT:        " << (int)(100 * (((double)satTime) / ((double)etime))) << endl;
		cout << ". K:            " << gipsat->level() << endl;
		cout << ". # Queries:    " << nQuery << endl;
		cout << ". # CTIs:       " << nCTI << endl;
		cout << ". # CTGs:       " << nCTG << endl;
		cout << ". # mic calls:  " << nmic << endl;
		cout << ". Queries/sec:  " << (int)(((double)nQuery) / ((double)etime) * sysconf(_SC_CLK_TCK)) << endl;
		cout << ". Mics/sec:     " << (int)(((double)nmic) / ((double)etime) * sysconf(_SC_CLK_TCK)) << endl;
		cout << ". # Red. cores: " << nCoreReduced << endl;
		cout << ". # Int. joins: " << nAbortJoin << endl;
		cout << ". # Int. mics:  " << nAbortMic << endl;
		if (numUpdates)
			cout << ". Avg lits/cls: " << numLits / numUpdates << endl;
	}

	friend bool check(Transys &, int, bool, bool);

	bool baseCases()
	{
		return !gipsat->has_bad();
	}
};

// IC3 does not check for 0-step and 1-step reachability, so do it
// separately.
bool baseCases(Model &model)
{
	Minisat::Solver *base0 = model.newSolver();
	model.loadInitialCondition(*base0);
	model.loadError(*base0);
	bool rv = base0->solve(model.error());
	delete base0;
	if (rv)
		return false;

	Minisat::Solver *base1 = model.newSolver();
	model.loadInitialCondition(*base1);
	model.loadTransitionRelation(*base1);
	rv = base1->solve(model.primedError());
	delete base1;
	if (rv)
		return false;

	model.lockPrimes();

	return true;
}

static void statistic()
{
	glabol_gipsat->statistic();
}

static void handle_int(int int_num)
{
	statistic();
	exit(0);
}

// External function to make the magic happen.
bool check(Transys &model, int verbose, bool basic, bool random)
{
	signal(SIGINT, handle_int);
	if (!baseCases(model)) {
		statistic();
		return false;
	}
	IC3 ic3(model);
	if (!ic3.baseCases()) {
		statistic();
		return false;
	}

	ic3.verbose = verbose;
	if (basic) {
		ic3.maxDepth = 0;
		ic3.maxJoins = 0;
		ic3.maxCTGs = 0;
	}
	if (random)
		ic3.random = true;
	bool rv = ic3.check();
	statistic();
	if (!rv && verbose > 1)
		ic3.printWitness();
	if (verbose)
		ic3.printStats();
	statistic();
	return rv;
}

}
