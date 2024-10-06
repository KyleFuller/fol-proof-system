# fol-proof-system (NOT MAINTAINED)
This repo is just a place to put some code I wrote at some point for a small project where I implemented a proof system for first order logic in Python.  It is not being developed or maintained as of now.  The proof system is implemented in a very minimalist fashion, with a “kernel” consisting only of expression types and rules for conditionals, negations, existentials, atomic terms (doubling as variables), and a membership relation (as I was intending specifically to use this for set theory and nothing else, really).  Everything else, including conjunctions, disjunctions, universals, and equalities, is implemented on top of this kernel.  There are no function symbols, because relations are arguably sufficient.  Expressions are implemented using interning so that there is only one copy of a given expression actually in existence at any point in time, and this is shared between expressions in which that expression appears.  This makes determining whether two expressions are the same much more efficient.

If I were to try this little project again, I would probably make it more general (not specific to set theory), include function symbols and maybe equality into the kernel, and implement a mechanism for actually extending the language with definitions of new connectives, predicates, functions, and perhaps quantifiers, rather than just implementing these new pieces of vocabulary as python functions that immediately expand to become their definitions.  This would probably be significantly more efficient in terms of time and space, and would also allow one to actually print expressions in the vocabulary in which they were written rather than the minimal kernel vocabulary to which they expand to.
