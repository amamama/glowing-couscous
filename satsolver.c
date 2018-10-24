#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <assert.h>


static inline size_t max(size_t const a, size_t const b) {
	return a < b ? b : a;
}

static inline size_t min(size_t const a, size_t const b) {
	return a < b ? a : b;
}

typedef struct bitset {
	size_t size;
	unsigned char set[];
} bitset_t, * bitset_p;

bitset_p alloc_bitset(size_t s) {
	bitset_p const ret = malloc(sizeof(bitset_t) + sizeof(unsigned char[s]));
	ret->size = s;
	memset(ret->set, 0, s);
	return ret;
}

#define free_bitset(s) (s?free(s), s = NULL:NULL)

bitset_p expand(bitset_p const set, size_t new_s) { //using arg set after returning this func is UB
	size_t const old_s = set->size;
	bitset_p const ret = realloc(set, sizeof(bitset_t) + sizeof(unsigned char[new_s]));
	ret->size = new_s;
	memset(ret->set + old_s, 0, new_s - old_s);
	return ret;
}

bitset_p expand_(bitset_p * const set, size_t new_s) { //using arg set after returning this func is UB
	*set = expand(*set, new_s);
	return *set;
}

bitset_p copy(bitset_p const s) {
	bitset_p const ret = alloc_bitset(s->size);
	memcpy(ret->set, s->set, s->size);
	return ret;
}

bitset_p copy_(bitset_p * const d, bitset_p const s) {
	if((*d)->size < s->size) expand_(d, s->size);
	memcpy((*d)->set, s->set, s->size);
	if((*d)->size > s->size) memset((*d)->set + s->size, 0, (*d)->size - s->size);
	return *d;
}

bitset_p cap(bitset_p const a, bitset_p const b) { //intersection
	size_t const s = min(a->size, b->size);
	bitset_p const ret = alloc_bitset(s);
	for(size_t i = 0; i < s; i++) ret->set[i] = a->set[i] & b->set[i];
	return ret;
}

bitset_p cap_(bitset_p const * const a, bitset_p const b) { //intersection
	size_t const s = min((*a)->size, b->size);
	for(size_t i = 0; i < s; i++) (*a)->set[i] &= b->set[i];
	return *a;
}

bitset_p cup(bitset_p const a, bitset_p const b) { //union
	size_t const sM = max(a->size, b->size), sm = min(a->size, b->size);
	bitset_p const ret = alloc_bitset(sM);
	for(size_t i = 0; i < sM; i++) ret->set[i] = a->set[i] | b->set[i];
	for(size_t i = sm; i < sM; i++) ret->set[i] = sm == b->size?a->set[i]:b->set[i];
	return ret;
}

bitset_p cup_(bitset_p * const a, bitset_p const b) { //union
	size_t const sM = max((*a)->size, b->size), sm = min((*a)->size, b->size);
	if((*a)->size < sM) expand_(a, sM);
	for(size_t i = 0; i < sm; i++) (*a)->set[i] |= b->set[i];
	for(size_t i = sm; i < sM; i++) (*a)->set[i] |= sm == b->size?(*a)->set[i]:b->set[i];
	return *a;
}

bitset_p dif(bitset_p const a, bitset_p const b) { // a - b
	bitset_p const ret = alloc_bitset(a->size);
	for(size_t i = 0; i < a->size; i++) ret->set[i] = a->set[i] & ~b->set[i];
	return ret;
}

bitset_p dif_(bitset_p const * const a, bitset_p const b) { //a - b
	for(size_t i = 0; i < (*a)->size; i++) (*a)->set[i] &= ~b->set[i];
	return *a;
}

bitset_p bar(bitset_p const s) {
	bitset_p const ret = alloc_bitset(s->size);
	for(size_t i = 0; i < s->size; i++) ret->set[i] = ~s->set[i];
	return ret;
}

bitset_p bar_(bitset_p const * const s) {
	for(size_t i = 0; i < (*s)->size; i++) (*s)->set[i] = ~(*s)->set[i];
	return *s;
}

bool get(bitset_p const s, size_t const i) {
	size_t q = i / 8, r = i % 8;
	if(s->size <= q) return 0;
	return !!(s->set[q] & 1 << r);
}

bitset_p set(bitset_p s, size_t const i, bool flag) {
	size_t q = i / 8, r = i % 8;
	if(!s) s = alloc_bitset(q + 1);
	if(s->size <= q) s = expand(s, q + 1); //+1 is for size
	s->set[q] = s->set[q] & ~(1u << r) | !!flag << r;
	return s;
}

bitset_p set_(bitset_p * const s, size_t const i, bool flag) {
	*s = set(*s, i, flag);
	return *s;
}

bool subset(bitset_p const a, bitset_p const b) { // a <= b
	size_t i = 0;
	for(i = 0; i < min(a->size, b->size); i++) if((a->set[i] & b->set[i]) != a->set[i]) return false;
	if(i == a->size) return true;
	for(; i < a->size; i++) if(a->set[i]) return false;
	return true;
}

bool equal(bitset_p const a, bitset_p const b) {
	return subset(a, b) && subset(b, a);
}

bool empty(bitset_p const s) {
	for(size_t i = 0; i < s->size; i++) if(s->set[i]) return false;
	return true;
}

typedef struct clause {
	bitset_p p_lit;
	bitset_p n_lit;
} clause_t, *clause_p;

clause_p alloc_clause(bitset_p const p, bitset_p const n) {
	clause_p ret = malloc(sizeof(clause_t));
	ret->p_lit = p;
	ret->n_lit = n;
	return ret;
}

#define free_clause(c) (c?free_bitset((c)->p_lit), free_bitset((c)->n_lit), free(c), c = NULL:NULL)

clause_p copy_clause(clause_p c) {
	return alloc_clause(copy(c->p_lit), copy(c->n_lit));
}

bool empty_clause(clause_p const c) {
	return empty(c->p_lit) && empty(c->n_lit);
}

typedef struct clause_list {
	size_t size;
	clause_p clauses[];
} clause_list_t, * clause_list_p;

clause_list_p alloc_clause_list(size_t const s) {
	clause_list_p ret = malloc(sizeof(clause_list_t) + sizeof(clause_p[s]));
	ret->size = s;
	memset(ret->clauses, 0, s);
	return ret;
}

void *free_clause_list(clause_list_p const l) {
	if(!l) return NULL;
	for(size_t i = 0, s = l->size; i < s; i++) free_clause(l->clauses[i]);
	free(l);
	return NULL;
}

clause_list_p copy_clause_list(clause_list_p const l) {
	clause_list_p ret = alloc_clause_list(l->size);
	for(size_t i = 0, s = l->size; i < s; i++) {
		ret->clauses[i] = l->clauses[i]?copy_clause(l->clauses[i]):NULL;
	}
	return ret;
}

#define free_clause_list(l) (free_clause_list(l),l = NULL)

bool empty_clause_list(clause_list_p const l) {
	for(size_t i = 0, s = l->size; i < s; i++) if(l->clauses[i]) return false;
	return true;
}

clause_list_p parse_dimacs(void) {
	int c = 0;
	for(;(c = getchar()) == 'c';) for(;getchar() != '\n';);
	ungetc(c, stdin);

	int varnum = 0, clausenum = 0, set_size = 0;
	scanf("p cnf %d %d", &varnum, &clausenum);
	set_size = varnum / 8 + 1;
	printf("varnum = %d, clausenum = %d\n", varnum, clausenum);
	if(clausenum < 1) return NULL;

	clause_list_p ret = alloc_clause_list(clausenum);
	for(int i = 0; i < clausenum; i++) {
		clause_p lit = alloc_clause(alloc_bitset(set_size), alloc_bitset(set_size));
		for(int idx = 0; scanf("%d", &idx), idx != 0;) {
			set(idx > 0?lit->p_lit:lit->n_lit, abs(idx), 1);
		}
		ret->clauses[i] = lit;
	}
	return ret;
}

clause_p preprocess_one_rule(clause_list_p const l) {
	clause_p ret = alloc_clause(alloc_bitset(0), alloc_bitset(0));
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i] || empty_clause(l->clauses[i])) continue;
		size_t litidx = 0;
		bool is_p = false, is_one_lit = false;
		for(size_t j = 0, s = l->clauses[i]->p_lit->size; j < s * 8; j++) {
			if(get(l->clauses[i]->p_lit, j)) {
				if(is_one_lit) goto cont;
				is_one_lit = true;
				litidx = j;
				is_p = true;
			}
			if(get(l->clauses[i]->n_lit, j)) {
				if(is_one_lit) goto cont;
				is_one_lit = true;
				litidx = j;
				is_p = false;
			}
		}
		set_(is_p?&ret->p_lit:&ret->n_lit, litidx, 1);
		//set(is_p?&var->p_lit:&var->n_lit, litidx, 1);
		cont:;
	}
	return ret;
}

clause_list_p exec_one_rule(clause_list_p const l, clause_p const one_lit) {
	clause_p mask_lit = alloc_clause(bar(one_lit->p_lit), bar(one_lit->n_lit));
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i]) continue;
		cap_(&l->clauses[i]->p_lit, mask_lit->n_lit);
		cap_(&l->clauses[i]->n_lit, mask_lit->p_lit);

		clause_p res = alloc_clause(cap(one_lit->p_lit, l->clauses[i]->p_lit), cap(one_lit->n_lit, l->clauses[i]->n_lit));
		if(!empty_clause(res)) free_clause(l->clauses[i]);
		free_clause(res);
	}
	free_clause(mask_lit);
	return l;
}

clause_p preprocess_pure_rule(clause_list_p const l) {
	bitset_p p_lit = alloc_bitset(0), n_lit = alloc_bitset(0);
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i]) continue;
		cup_(&p_lit, l->clauses[i]->p_lit);
		cup_(&n_lit, l->clauses[i]->n_lit);
	}
	clause_p ret = alloc_clause(dif(p_lit, n_lit), dif(n_lit, p_lit));
	//cup_(var->p_lit, ret->p_lit);
	//cup_(var->n_lit, ret->n_lit);
	free_bitset(p_lit);
	free_bitset(n_lit);
	return ret;
}

clause_list_p exec_pure_rule(clause_list_p const l, clause_p const pure_lit) {
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i]) continue;
		clause_p res = alloc_clause(cap(l->clauses[i]->p_lit, pure_lit->p_lit), cap(l->clauses[i]->n_lit, pure_lit->n_lit));
		if(!empty(res->p_lit) || !empty(res->n_lit)) free_clause(l->clauses[i]);
		free_clause(res);
	}
	return l;
}

clause_list_p exec_cleanup_rule(clause_list_p const l) {
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i]) continue;
		bitset_p res = cap(l->clauses[i]->p_lit, l->clauses[i]->n_lit);
		if(!empty(res)) free_clause(l->clauses[i]);
		free_bitset(res);
	}
	return l;
}

bitset_p preprocess_splitting_rule(clause_list_p const l) {
	for(size_t i = 0, s = l->size; i < s; i++) {
		if(!l->clauses[i]) continue;
		bitset_p bs = alloc_bitset(0);
		for(size_t j = 0, s = l->clauses[i]->p_lit->size; j < s * 8; j++) if(get(l->clauses[i]->p_lit, j)) return set_(&bs, j, 1);
		for(size_t j = 0, s = l->clauses[i]->n_lit->size; j < s * 8; j++) if(get(l->clauses[i]->n_lit, j)) return set_(&bs, j, 1);
	}
	return alloc_bitset(0);
}

clause_list_p exec_splitting_rule(clause_list_p const l, bitset_p const split_lit) {
	clause_p p_cl = alloc_clause(split_lit, alloc_bitset(0)), n_cl = alloc_clause(alloc_bitset(0), copy(split_lit));
	clause_list_p ret = copy_clause_list(l);
	exec_one_rule(l, p_cl);
	exec_one_rule(ret, n_cl);
	free_clause(p_cl);
	free_clause(n_cl);
	return ret;
}

#define printf(...) (__VA_ARGS__)
#define print_bitset(e) (e)
#define print_clause(e) (e)
#define print_clause_list(e) (e)

clause_p dpll(clause_list_p const l) {
	clause_p ret = alloc_clause(alloc_bitset(0), alloc_bitset(0));
	for(bool empty_o = false, empty_p = false; !(empty_o && empty_p); ) {
		print_clause_list(l);
		clause_p o = preprocess_one_rule(l), p = preprocess_pure_rule(l);
		exec_one_rule(l, o);
		exec_pure_rule(l, p);
		empty_o = empty_clause(o);
		empty_p = empty_clause(p);
		print_clause(o);
		print_clause(p);
		//print_clause(ret); puts("");
		cup_(&ret->p_lit, o->p_lit);
		cup_(&ret->p_lit, p->p_lit);
		cup_(&ret->n_lit, o->n_lit);
		cup_(&ret->n_lit, p->n_lit);
		free_clause(o);
		free_clause(p);
		getchar();
	}
	//puts("dpll");


	if(empty_clause_list(l)) return ret;
	for(size_t i = 0, s = l->size; i < s; i++) if(l->clauses[i] && empty_clause(l->clauses[i])) return NULL;

	bitset_p split = preprocess_splitting_rule(l), v = NULL;
	v = copy(split);
	clause_list_p new_l = exec_splitting_rule(l, split);
	clause_p p_ret = dpll(l), n_ret = dpll(new_l);
	if(p_ret) cup_(&ret->p_lit, v), cup_(&ret->p_lit, p_ret->p_lit), cup_(&ret->n_lit, p_ret->n_lit);
	else if(n_ret) cup_(&ret->n_lit, v), cup_(&ret->p_lit, n_ret->p_lit), cup_(&ret->n_lit, n_ret->n_lit);
	else free_clause(ret);

	free_clause_list(new_l);
	free_bitset(v);
	free_clause(p_ret);
	free_clause(n_ret);

	return ret;
}
#undef printf
#undef print_bitset
#undef print_clause
#undef print_clause_list

int print_bitset(bitset_p s) {
	if(!s) return 0;
	for(int i = 0; i < s->size * 8; i++) if(get(s, i)) printf(" %d", i);
	return 0;
}

int print_clause(clause_p c) {
	if(!c) return printf("{}");
	printf("{p");
	print_bitset(c->p_lit);
	printf(" n");
	print_bitset(c->n_lit);
	printf("}");
	return 0;
}

int print_clause_list(clause_list_p l) {
	if(!l) return 0;
	for(size_t i = 0; i < l->size; i++) print_clause(l->clauses[i]), puts("");
	return 0;
}

int main(void) {
	clause_list_p l = parse_dimacs();
	clause_p var = NULL;
	//print_clause_list(l);
	exec_cleanup_rule(l);
	(var = dpll(l))?print_clause(var):puts("unsat");

}