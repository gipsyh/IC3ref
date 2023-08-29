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
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	p->sharer = sharer;
}

static void pic3ic3ref_diversify(void *t, int rank, int size)
{
}

static int pic3ic3ref_solve(void *t)
{
	struct Pic3Ic3ref *p = (struct Pic3Ic3ref *)t;
	return IC3::check(*p->model, p->sharer, 1, false, false);
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