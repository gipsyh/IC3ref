#include "TransSolver.h"
#include "bits/stdc++.h"
using namespace std;
using namespace Tocadical;

Solver::Solver()
	: next_var(0)
{
	slv = new CaDiCaL::Solver();
}

Solver::~Solver()
{
	delete slv;
}

Var Solver::newVar()
{
	Var v;
	v = next_var++;
	return v;
}

int Solver::getLit(Lit p)
{
	if (Minisat::sign(p))
		return -(Minisat::var(p) + 1);
	else
		return Minisat::var(p) + 1;
}

bool Solver::addClause(const Minisat::vec<Lit> &ps)
{
	for (int i = 0; i < ps.size(); i++) {
		slv->add(getLit(ps[i]));
	}
	slv->add(0);
	return false;
}

bool Solver::addClause(Lit p)
{
	slv->clause(getLit(p));
	return true;
}
bool Solver::addClause(Lit p, Lit q)
{
	slv->clause(getLit(p), getLit(q));
	return true;
}
bool Solver::addClause(Lit p, Lit q, Lit r)
{
	slv->clause(getLit(p), getLit(q), getLit(r));
	return true;
}
bool Solver::addClause(Lit p, Lit q, Lit r, Lit s)
{
	slv->clause(getLit(p), getLit(q), getLit(r), getLit(s));
	return true;
}

bool Solver::addClause_(Minisat::vec<Lit> &ps)
{
	for (int i = 0; i < ps.size(); i++) {
		slv->add(getLit(ps[i]));
	}
	slv->add(0);
	return true;
}

bool Solver::solve(const Minisat::vec<Lit> &assumps)
{
	for (int i = 0; i < assumps.size(); i++) {
		slv->assume(getLit(assumps[i]));
	}
	int res = slv->solve();
	if (res == 10)
		return true;
	else if (res == 20)
		return false;
}

bool Solver::solve(Lit p)
{
	slv->assume(getLit(p));
	int res = slv->solve();
	if (res == 10)
		return true;
	else if (res == 20)
		return false;
}

lbool Solver::modelValue(Var x) const
{
	int res = slv->val(x + 1);
	if (res > 0)
		return Minisat::l_True;
	else
		return Minisat::l_False;
}

bool Solver::has(Lit p)
{
	bool res = slv->failed(getLit(p));
	return res;
}

int Solver::nVars()
{
	return next_var;
}

void Solver::releaseVar(Lit p)
{
	addClause(p);
}

void Solver::simplify()
{
	slv->simplify();
}