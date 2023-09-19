#include "pic3.h"
#include "Model.h"
#include "IC3.h"
extern "C" {
#include "aiger/aiger.h"
}

static aiger *aig;

struct Pic3Ic3ref {
	int verbose;
	int random_seed;
	struct Synchronizer synchronizer;
};

static void *pic3ic3ref_create()
{
	struct Pic3Ic3ref *ic3ref = (struct Pic3Ic3ref *)malloc(sizeof(struct Pic3Ic3ref));
	ic3ref->verbose = 0;
	ic3ref->random_seed = rand();
	return ic3ref;
}

static void pic3ic3ref_set_model(void *t, char *model)
{
	if (aig == NULL) {
		FILE *aig_file = fopen(model, "r");
		aig = aiger_init();
		aiger_read_from_file(aig, aig_file);
		fclose(aig_file);
	}
}

static void pic3ic3ref_set_synchronizer(void *t, struct Synchronizer synchronizer)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	p->synchronizer = synchronizer;
}

static void pic3ic3ref_set_random_seed(void *t, int random)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	p->random_seed = random;
}

static void pic3ic3ref_diversify(void *t, int rank, int size)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	if (rank == 0) {
		p->verbose = 1;
	}
}

static int pic3ic3ref_solve(void *t)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	Model *model = modelFromAiger(aig, 0);
	return IC3::check(*model, p->synchronizer, p->verbose, false, true, p->random_seed);
}

struct Pic3Interface pic3ic3ref = {
	.create = pic3ic3ref_create,
	.set_model = pic3ic3ref_set_model,
	.set_synchronizer = pic3ic3ref_set_synchronizer,
	.set_random_seed = pic3ic3ref_set_random_seed,
	.diversify = pic3ic3ref_diversify,
	.solve = pic3ic3ref_solve,
};

void pic3_share_lemma(struct Synchronizer *synchronizer, int k, LitVec &cube)
{
	int *lits = (int *)malloc(sizeof(int) * cube.size());
	for (int i = 0; i < cube.size(); i++) {
		lits[i] = (cube[i]).x;
	}
	struct Lemma lemma = {
		.frame_idx = k,
		.lits = lits,
		.num_lit = cube.size(),
	};
	(synchronizer->share_lemma)(synchronizer->data, lemma);
}
