#include "pic3.h"
#include "Model.h"
#include "IC3.h"
extern "C" {
#include "aiger/aiger.h"
}

static aiger *aig;

struct Pic3Ic3ref {
	int verbose;
	struct LemmaSharer sharer;
};

static void *pic3ic3ref_create()
{
	struct Pic3Ic3ref *ic3ref =
		(struct Pic3Ic3ref *)malloc(sizeof(struct Pic3Ic3ref));
	if (aig == NULL) {
		FILE *aig_file = fopen(
			// "/root/MC-Benchmark/hwmcc20/aig/2019/beem/pgm_protocol.7.prop1-back-serstep.aig",
			"/root/MC-Benchmark/examples/counter/10bit/counter.aig",
			"r");
		aig = aiger_init();
		aiger_read_from_file(aig, aig_file);
		fclose(aig_file);
	}

	return ic3ref;
}

static void pic3ic3ref_set_lemma_sharer(void *t, struct LemmaSharer sharer)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	p->sharer = sharer;
	p->verbose = 0;
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
	return IC3::check(*model, p->sharer, p->verbose, false, false);
}

struct Pic3Interface pic3ic3ref = {
	.create = pic3ic3ref_create,
	.set_lemma_sharer = pic3ic3ref_set_lemma_sharer,
	.diversify = pic3ic3ref_diversify,
	.solve = pic3ic3ref_solve,
};

void pic3_share_lemma(struct LemmaSharer *sharer, int k, LitVec &cube)
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
	(sharer->share)(sharer->data, lemma);
}

// void pic3_acquire_lemma(Pdr_Man_t *p)
// {
// 	while (1) {
// 		struct Lemma lemma =
// 			p->pic3.sharer.acquire(p->pic3.sharer.data);
// 		if (lemma.lits == NULL) {
// 			break;
// 		}
// 		Vec_Int_t lits = { .nCap = lemma.num_lit,
// 				   .nSize = lemma.num_lit,
// 				   .pArray = lemma.lits };
// 		Vec_Int_t *pilits = Vec_IntAlloc(0);
// 		Pdr_Set_t *cube = Pdr_SetCreate(&lits, pilits);
// 		ABC_FREE(lits.pArray);
// 		Vec_IntFree(pilits);
// 		if (Pdr_ManCheckContainment(p, lemma.frame_idx, cube)) {
// 			Pdr_SetDeref(cube);
// 			continue;
// 		} else {
// 			if (Vec_PtrSize(p->vClauses) > lemma.frame_idx) {
// 				Vec_VecPush(p->vClauses, lemma.frame_idx, cube);
// 				for (int i = 1; i <= lemma.frame_idx; i++)
// 					Pdr_ManSolverAddClause(p, i, cube);
// 			}
// 		}
// 	}
// }