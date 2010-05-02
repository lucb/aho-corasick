/*
 * Simple implementation of the Aho-Corasick algorithm
 *
 * Efficient String Matching: An Aid to Bibliographic Search 
 * Alfred V. Aho and Margaret J. Corasick 
 *
 */

#include "AhoCorasick.h"

#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <sys/queue.h>

typedef unsigned int State;
#define FAIL_STATE UINT_MAX
typedef char Symbol;


typedef SLIST_HEAD( _transitions_list, transition_elt) transitions_list;
struct transition_elt {
	Symbol		sym;
	State		st;
	SLIST_ENTRY(transition_elt) entries;
};

typedef SLIST_HEAD( _string_list, string_node) string_list;
struct string_node
{
#ifdef STORE_DICTIONARY_ELT
	/* this is used if the strings are explicitly store in the structure */
    char *str;
#else
	/* with the byte length and the offset of the last character, once
	 * it matched, the original string can be rebuilt. */
	unsigned int blen;
#endif	/* STORE_DICTIONARY_ELT */
	SLIST_ENTRY(string_node) entries;
};											   

struct _string_matcher {
	transitions_list	 *trans_matrix; /* adjacency matrix */
	string_list			 *output;		/* lists of pointers in the dictionary for output states */
	State				 *failure;		/* Failure states */
	unsigned int		  n;			/* number of states in the machine*/
	unsigned int		  sz;			/* allocated number of states */
	Symbol				 *alphabet;		/* symbols used in the dictionary */
	unsigned int		  n_alpha;		/* number of symbols in alphabet */
	unsigned int		  sz_alpha;		/* allocated numbers of symbols */
#ifdef STORE_DICTIONARY_ELT
	short int			 *dictionary;	/* array of string to search length */
	unsigned int		  n_words;		/* number of strings to search */
#endif
};

static struct _string_matcher * init_string_matcher(unsigned int sz);
static State new_state(struct _string_matcher * p_sm);
static int add_symbol(struct _string_matcher * p_sm, Symbol symbol);
static int add_transition(struct _string_matcher * p_sm,
						  State start, Symbol symbol, State end);
static State goto_state(const struct _string_matcher *p_sm,
						State state, Symbol symbol);
static State fail_state(const struct _string_matcher * p_sm, State s);
static string_list * output_state(const struct _string_matcher * p_sm,
								  State state);
#ifdef STORE_DICTIONARY_ELT
static int add_output_state(struct _string_matcher * p_sm,
							State state, char *str);
#else
static int add_output_state(struct _string_matcher * p_sm,
							State state, unsigned int blen);
#endif
static struct _string_matcher * create_goto_function(int n, char * patterns[n]);
static void create_failure_function(struct _string_matcher * p_sm);

string_matcher
new_string_matcher( int n, char *patterns[n])
{
	struct _string_matcher * p_sm;

	p_sm = create_goto_function(n, patterns);
	create_failure_function(p_sm);

	return p_sm;
}

void
free_string_matcher(struct _string_matcher *p_sm)
{
	int i;
	if (p_sm != NULL) {
		for (i = 0; i < p_sm->n; i++) {
			transitions_list *head;
			head = & (p_sm->trans_matrix[i]);
			while (!SLIST_EMPTY(head)) {
				struct transition_elt *p_trelt;
				p_trelt = SLIST_FIRST(head);
				SLIST_REMOVE_HEAD(head, entries);
				free(p_trelt);
			}
		}
		free(p_sm->trans_matrix);

		for ( i = 0; i < p_sm->n; i++) {
			string_list *head;
			head = & (p_sm->output[i]);
			while (!SLIST_EMPTY(head)) {
				struct string_node *p_str;
				p_str = SLIST_FIRST(head);
				SLIST_REMOVE_HEAD(head, entries);
				free(p_str);
			}
		}
		free(p_sm->output);

		free(p_sm->failure);

		if (p_sm->alphabet != NULL)
			free(p_sm->alphabet);

#ifdef STORE_DICTIONARY_ELT
		if (p_sm->dictionary != NULL) {
			for ( i = 0; i < p_sm->n_words; i++)
				free(p_sm->dictionary[i]);
			free(p_sm->dictionary);
		}
#endif	/* STORE_DICTIONARY_ELT */
		free(p_sm);
	}
}

unsigned int
find_matched_string( struct matches **hits,
					 const string_matcher sm, const char* text)
{
	int len;
	int i;

	struct matches *results;
	int sz;
	sz = 64;
	results = malloc(sizeof(*results));
	results->n = 0;
	results->match = calloc(sz, sizeof(results->match));

	
	State state;
	state = 0;

#ifdef DEBUG
	printf("text: %s\n", text);
#endif
	len = strlen(text);
	for (i = 0; i < len; i++) {
#ifdef DEBUG
		printf("text[%d]: %c\n", i, text[i]);
#endif
		while (goto_state(sm, state, text[i]) == FAIL_STATE) { /* fail */
			state = fail_state(sm, state);
		}
		state = goto_state(sm, state, text[i]);
		if (! SLIST_EMPTY(output_state(sm, state))) {
#ifdef DEBUG
			printf("match in state : %d\n", state);
#endif
			struct string_node *pn;
			SLIST_FOREACH(pn, output_state(sm, state), entries) {
				if (results->n >= sz) {
					sz +=64;
					results->match = realloc(results->match,
											 sz * sizeof(results->match[0]));
				}
#ifdef STORE_DICTIONARY_ELT
				results->match[count].blen = strlen(pn->str);
#else  /* ! STORE_DICTIONARY_ELT */
				results->match[results->n].blen = pn->blen;
#endif	/* ! STORE_DICTIONARY_ELT */
				results->match[results->n].boff
					= i - results->match[results->n].blen + 1;
				results->n++;
#ifdef DEBUG
#ifdef STORE_DICTIONARY_ELT
				printf("\ttext [%d..%d] : %s\n", i - strlen(pn->str) + 1, i, pn->str);
#else	/* ! STORE_DICTIONARY_ELT */
				printf("\ttext [%d..%d] : %.*s\n",
					   i - pn->blen + 1, i, pn->blen, text + ( i - pn->blen + 1));
#endif	/* STORE_DICTIONARY_ELT */
#endif	/* DEBUG */
			}
		}
	}
	*hits = results;
	return results->n;
}

struct _string_matcher *
init_string_matcher(unsigned int sz)
{
	struct _string_matcher * p_sm;

	p_sm = malloc(sizeof(*p_sm));

	p_sm->trans_matrix = calloc(sz, sizeof(p_sm->trans_matrix[0]));
	p_sm->output	   = calloc(sz, sizeof(p_sm->output[0]));
	p_sm->failure	   = calloc(sz, sizeof(p_sm->failure[0]));

	p_sm->n  = 0;
	p_sm->sz = sz;

	p_sm->n_alpha  = 0;
	p_sm->sz_alpha = 64;
	p_sm->alphabet = calloc(p_sm->sz_alpha, sizeof(p_sm->alphabet[0]));

	return p_sm;
}

State
new_state(struct _string_matcher * p_sm)
{
	if (p_sm->n >= p_sm->sz) {
		unsigned int sz = p_sm->sz;
		sz += 1024;
		p_sm->trans_matrix = realloc(p_sm->trans_matrix,
									 sz * sizeof(p_sm->trans_matrix[0]));
		p_sm->output = realloc(p_sm->output,
							   sz * sizeof(p_sm->output[0]));
		p_sm->failure = realloc(p_sm->failure,
								sz * sizeof(p_sm->failure[0]));
		p_sm->sz = sz;
	}
	State new_state = p_sm->n;
	p_sm->n++;
	SLIST_INIT(& p_sm->trans_matrix[new_state]);
	SLIST_INIT(& p_sm->output[new_state]);
	p_sm->failure[new_state] = 0;

	return new_state;
}

int
add_symbol(struct _string_matcher * p_sm, Symbol symbol)
{
	int i;
	for ( i = 0; i < p_sm->n_alpha; i++) {
		if (symbol == p_sm->alphabet[i])
			return i;
	}
	if (p_sm->n_alpha == p_sm->sz_alpha) {
		unsigned int sz;
		sz = p_sm->sz_alpha * 2;
		p_sm->alphabet = realloc(p_sm->alphabet,
								 sz * sizeof(p_sm->alphabet[0]));
		p_sm->sz_alpha = sz;
	}
	p_sm->alphabet[i] = symbol;
	p_sm->n_alpha++;

	return i;
}

int
add_transition(struct _string_matcher * p_sm,
			   State start, Symbol symbol, State end)
{
	struct transition_elt		*elt;
	elt		 = malloc(sizeof(*elt));
	elt->sym = symbol;
	elt->st	 = end;
	SLIST_INSERT_HEAD(& (p_sm->trans_matrix[start]), elt, entries);
	add_symbol(p_sm, symbol);
	return 1;
}

State
goto_state(const struct _string_matcher *p_sm, State state, Symbol symbol)
{
	transitions_list			*tlist;
	struct transition_elt		*transition;
	
	if (state >= p_sm->n)
		return FAIL_STATE;
	tlist = & p_sm->trans_matrix[state];

	SLIST_FOREACH( transition , tlist, entries) {
		if(transition->sym == symbol)
			return transition->st;
	}
	if (state == 0)
		return 0;
	return FAIL_STATE;
}

State
fail_state(const struct _string_matcher * p_sm, State s)
{
	if (s < p_sm->n)
		return p_sm->failure[s];
	else
		return 0;
}

string_list *
output_state(const struct _string_matcher * p_sm, State state)
{
	if (state < p_sm->n)
		return & p_sm->output[state];

	return & p_sm->output[state];		/* this could spell trouble */
}

#ifdef STORE_DICTIONARY_ELT
int
add_output_state(struct _string_matcher * p_sm,
				 State state, char *str)
{
	struct string_node *node;

	node = malloc(sizeof(*node));

	node->str = str;
	SLIST_INSERT_HEAD( &(p_sm->output[state]), node, entries);
	return 0;
}
#else  /* ! STORE_DICTIONARY_ELT */
int
add_output_state(struct _string_matcher * p_sm,
				 State state, unsigned int blen)
{
	struct string_node *node;

	node = malloc(sizeof(*node));

	node->blen = blen;
	SLIST_INSERT_HEAD( &(p_sm->output[state]), node, entries);
	return 0;
}
#endif	/* ! STORE_DICTIONARY_ELT */

struct _string_matcher *
create_goto_function(int n, char * patterns[n])
{
	struct _string_matcher * p_sm;

	p_sm = init_string_matcher(128);

#ifdef STORE_DICTIONARY_ELT
	p_sm->n_words = n;
	p_sm->dictionary = calloc(p_sm->n_words, sizeof(p_sm->dictionary[0]));
#endif

	/* building the Trie */
	const State initial_state = new_state(p_sm); /* Initialize root node */

	State newstate;
	int i;
	for (i = 0; i < n; i++) {
		char	*pattern;
		State	 state;
		State	 s;
		int		 j;
		int		 lp;
		
		pattern = patterns[i];
		state	= initial_state;
		j		= 0;
		lp		= strlen(pattern);
		while (j < lp) {
			s = goto_state(p_sm, state, pattern[j]);
			if ((s == FAIL_STATE) || ((state == 0) && (s == 0)))
				break;
			state = goto_state(p_sm, state, pattern[j]);
			j++;
		}

		int k;
		for (k = j; k < lp; k++) { // each remaining characters
			newstate = new_state(p_sm);
			add_transition(p_sm, state, pattern[k], newstate);
			state = newstate;
		}
		/* keep track of the inserted ending space (if needed) */
		/*
		newstate = new_state(p_sm);
		add_transition(trans_mat, state, ' ', newstate);
		state = newstate;
		*/
#ifdef STORE_DICTIONARY_ELT
		p_sm->dictionary[i] = strdup(patterns[i]);
		add_output_state(p_sm, state, p_sm->dictionary[i]);
#else
		add_output_state(p_sm, state, strlen(patterns[i]));
#endif
	}
	/* Pad the transition matrix. (Unnecessary for sparse matrix) */
	/*
	forall character c {
		if ( goto_state(trans_mat, 0, c) == NULL )
			add_transition(trans_mat, 0, c, NULL);
			}
	*/
	return p_sm;
}

/*
 * Keep track of the longest matching suffix of the characters we have
 * processed.
 *
 * Traverse the transition matrix in a breadth-first approach.
 */
void
create_failure_function(struct _string_matcher * p_sm)
{
	STAILQ_HEAD(stailhead, entry) queue_head =
		STAILQ_HEAD_INITIALIZER(queue_head);
	struct entry {
		State state;
		STAILQ_ENTRY(entry) entries;
	} *p_st1, *p_st2;
	STAILQ_INIT(&queue_head);
	
	/* enqueue all the State reachable in one step from the root */
	/* foreach letter in alphabet do */
	Symbol		letter;	
	State		s;
	int			i;
	for ( i = 0; i < p_sm->n_alpha; i++) {
		letter = p_sm->alphabet[i];
		s = goto_state(p_sm, 0, letter);
		if ((s != FAIL_STATE) && (s != 0)) {			/* s != fail */
			/* a kind of "unification" */
			p_sm->failure[s] = 0;
			p_st1 = malloc(sizeof(*p_st1));
			p_st1->state = s;
			STAILQ_INSERT_TAIL(& queue_head, p_st1, entries); /* enqueue */
		}
	}
	while(!STAILQ_EMPTY(& queue_head)) {
		p_st1 = STAILQ_FIRST(& queue_head); /* dequeue */
		STAILQ_REMOVE_HEAD(& queue_head, entries);
		/* foreach letter in the alphabet do */
		for ( i = 0; i < p_sm->n_alpha; i++) {
			letter = p_sm->alphabet[i];
			s = goto_state(p_sm, p_st1->state, letter);
			if  (s != FAIL_STATE) {		/* s != fail */
				p_st2 = malloc(sizeof(*p_st2));
				p_st2->state = s;
				STAILQ_INSERT_TAIL(& queue_head, p_st2, entries); /* enqueue */

				/* problematic code */
				State state;
				state = fail_state( p_sm, p_st1->state);
				while ( (goto_state( p_sm, state, letter) == FAIL_STATE)
						&& (state != 0)) {
					state = fail_state( p_sm, state);
				}
				if ((state == 0) && (goto_state(p_sm, state, letter) == FAIL_STATE))
					p_sm->failure[s] = 0;
				else
					p_sm->failure[s] = goto_state(p_sm, state, letter);

				string_list *str_lst;
				struct string_node *p_str_node;
				str_lst = output_state(p_sm, fail_state( p_sm, s));
				SLIST_FOREACH(p_str_node, str_lst, entries) {
#ifdef STORE_DICTIONARY_ELT
					add_output_state(p_sm, s, p_str_node->str);
#else
					add_output_state(p_sm, s, p_str_node->blen);
#endif	/* STORE_DICTIONARY_ELT */
				}
			}
		}
		free(p_st1);
	}
}

void
print_string_matcher(const struct _string_matcher * p_sm, FILE *fp)
{
	int							 i;
	struct transition_elt		*tr;
	struct string_node *p_str_node;

	fprintf(fp, "** string matching machine [BEGIN] **\n");
	for ( i = 0; i < p_sm->n; i++) {
		SLIST_FOREACH ( tr, & p_sm->trans_matrix[i], entries) {
			fprintf(fp, "%4d\t %4c -> %u\n", i, tr->sym, tr->st);
		}
		fprintf(fp, "%4d\t fail -> %u\n", i, fail_state(p_sm, i));
		SLIST_FOREACH ( p_str_node, & p_sm->output[i], entries) {
#ifdef STORE_DICTIONARY_ELT
			fprintf(fp, "%4d\t out  -> %s\n", i, p_str_node->str);
#else
			fprintf(fp, "%4d\t out  -> %u\n", i, p_str_node->blen);
#endif
		}
	}
	fprintf(fp, "** string matching machine [END] **\n");	
}

#ifdef DEBUG
int
main(int argc, char const *argv[])
{
	string_matcher		 sm;
	struct matches		*hits;
	int i, nm;
	
	char* text[] = {"aabcbaa",
					"ushers"};
	char *patterns0[] = {"bb", "abc", "bcb", "aabc", "bca", "aa"};

	char *patterns1[] = {"he", "she", "his", "hers"};

	sm = new_string_matcher( sizeof(patterns0)/sizeof(*patterns0),
							 patterns0);
	print_string_matcher( sm, stdout);
	nm = find_matched_string( &hits, sm, text[0]);
	printf("%d match%s found\n\n", nm, (nm > 1) ? "es" : "");
	for ( i = 0; i < hits->n; i++) {
		printf("%d) %.*s\n", i, hits->match[i].blen, text[0] + hits->match[i].boff);
	}
	free_string_matcher( sm );
	free(hits->match);
	free(hits);
	
	sm = new_string_matcher( sizeof(patterns1)/sizeof(*patterns1),
							 patterns1);
	print_string_matcher( sm, stdout );
	nm = find_matched_string( &hits, sm, text[1]);
	printf("%d match%s found\n\n", nm, (nm > 1) ? "es" : "");
	for ( i = 0; i < hits->n; i++) {
		printf("%d) %.*s\n", i, hits->match[i].blen, text[1] + hits->match[i].boff);
	}
	free_string_matcher( sm );
	free(hits->match);
	free(hits);

	return EXIT_SUCCESS;
}
#endif	/* DEBUG */
