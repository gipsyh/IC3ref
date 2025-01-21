#ifndef TRANSSOLVER_H_INCLUDED
#define TRANSSOLVER_H_INCLUDED

#include "cryptominisat/src/cryptominisat.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#include <assert.h>
#include <vector>
#include <algorithm>
#include <unordered_set>

using std::vector;

namespace ToCMsat
{

typedef Minisat::Lit Lit;
typedef Minisat::lbool lbool;
typedef int Var;

class Solver {
    public:
	Solver();
	~Solver();

	Var newVar();
	bool addClause(const Minisat::vec<Lit> &ps);
	bool addClause(Lit p); // Add a unit clause to the solver.
	bool addClause(Lit p, Lit q); // Add a binary clause to the solver.
	bool addClause(Lit p, Lit q, Lit r); // Add a ternary clause to the solver.
	bool addClause(Lit p, Lit q, Lit r, Lit s);
	bool addClause_(Minisat::vec<Lit> &ps);
	bool solve(const Minisat::vec<Lit> &assumps); // Search for a model that respects a given set of assumptions.
	bool solve(Lit p); // Search for a model that respects a single assumption.
	lbool modelValue(Var x) const;
	void releaseVar(Lit p);
	bool has(Lit p);
	int nVars();
	void simplify();
	CMSat::Lit litchange(Lit p);

    private:
	CMSat::SATSolver *slv;
	std::unordered_set<int> *core;
};

}

#endif