
typedef struct _string_matcher * string_matcher;

struct matches {
	unsigned int n;
	struct {
		unsigned int boff;
		unsigned int blen;
	} *match;
};

string_matcher	new_string_matcher( int n, char * patterns[n]);
void			free_string_matcher( string_matcher);

unsigned int find_matched_strings( struct matches **hits,
								   const string_matcher, const char *);

