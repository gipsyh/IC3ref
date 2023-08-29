#include "pic3.h"
#include "Model.h"
#include "IC3.h"
extern "C" {
	#include "aiger/aiger.h"
}

struct Pic3Ic3ref {
	Model *model;
	struct LemmaSharer sharer;
};

static void *pic3ic3ref_create()
{
	struct Pic3Ic3ref *ic3ref =
		(struct Pic3Ic3ref *)malloc(sizeof(struct Pic3Ic3ref));
	FILE *aig_file = fopen(
		"/root/MC-Benchmark/hwmcc20/aig/2019/beem/pgm_protocol.7.prop1-back-serstep.aig",
		"r");
	aiger *aig = aiger_init();
	aiger_read_from_file(aig, aig_file);
	ic3ref->model = modelFromAiger(aig, 0);
	return ic3ref;
}

static void pic3ic3ref_set_lemma_sharer(void *t, struct LemmaSharer sharer)
{
}

static void pic3ic3ref_diversify(void *t, int rank, int size)
{
}

static int pic3ic3ref_solve(void *t)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	return IC3::check(*p->model, 0, false, false);
}

struct Pic3Interface pic3ic3ref = {
	.create = pic3ic3ref_create,
	.set_lemma_sharer = pic3ic3ref_set_lemma_sharer,
	.diversify = pic3ic3ref_diversify,
	.solve = pic3ic3ref_solve,
};
