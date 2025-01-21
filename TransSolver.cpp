#include "TransSolver.h"
#include <unordered_set>
using namespace ToCMsat;
using std::vector;

Solver::Solver()
{
	slv = new CMSat::SATSolver();
	core = NULL;
}

Solver::~Solver()
{
	delete slv;
}

Var Solver::newVar()
{
	slv->new_var();
	return nVars() - 1;
}

bool Solver::addClause(const Minisat::vec<Lit> &ps)
{
	vector<CMSat::Lit> clause;
	for (int i = 0; i < ps.size(); i++) {
		clause.push_back(litchange(ps[i]));
	}
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::addClause(Lit p)
{
	vector<CMSat::Lit> clause;
	clause.push_back(litchange(p));
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::addClause(Lit p, Lit q)
{
	vector<CMSat::Lit> clause;
	clause.push_back(litchange(p));
	clause.push_back(litchange(q));
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::addClause(Lit p, Lit q, Lit r)
{
	vector<CMSat::Lit> clause;
	clause.push_back(litchange(p));
	clause.push_back(litchange(q));
	clause.push_back(litchange(r));
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::addClause(Lit p, Lit q, Lit r, Lit s)
{
	vector<CMSat::Lit> clause;
	clause.push_back(litchange(p));
	clause.push_back(litchange(q));
	clause.push_back(litchange(r));
	clause.push_back(litchange(s));
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::addClause_(Minisat::vec<Lit> &ps)
{
	vector<CMSat::Lit> clause;
	for (int i = 0; i < ps.size(); i++) {
		clause.push_back(litchange(ps[i]));
	}
	const vector<CMSat::Lit> &clause_ = clause;
	return slv->add_clause(clause_);
}

bool Solver::solve(const Minisat::vec<Lit> &assumps)
{
	if (core != NULL) {
		delete core;
		core = NULL;
	}
	vector<CMSat::Lit> new_assumps;
	for (int i = 0; i < assumps.size(); i++) {
		new_assumps.push_back(litchange(assumps[i]));
	}
	CMSat::lbool res = slv->solve(&new_assumps);
	return (bool)!(res.getValue());
}

bool Solver::solve(Lit p)
{
	if (core != NULL) {
		delete core;
		core = NULL;
	}
	vector<CMSat::Lit> assumps;
	assumps.push_back(litchange(p));
	CMSat::lbool res = slv->solve(&assumps);
	return (bool)!(res.getValue());
}

lbool Solver::modelValue(Var x) const
{
	const vector<CMSat::lbool> &model = slv->get_model();

	return Minisat::lbool((u_int8_t)CMSat::toInt(model[x]));
}

bool Solver::has(Lit p)
{
	if (core == NULL) {
		const vector<CMSat::Lit> &conflict = slv->get_conflict();
		core = new std::unordered_set<int>();
		for (auto &l : conflict) {
			core->insert(l.toInt());
		}
	}
	return core->count(toInt(p)) > 0;
}

void Solver::releaseVar(Lit p)
{
	Solver::addClause(p);
}

int Solver::nVars()
{
	return slv->nVars();
}

void Solver::simplify()
{
	slv->simplify();
}

CMSat::Lit Solver::litchange(Lit p)
{
	return CMSat::Lit(Minisat::var(p), Minisat::sign(p));
}