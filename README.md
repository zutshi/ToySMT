# ToySMT - simple SMT solver under ~1500 SLOC of pure C.

It's very early sneak preview.
It supports only bools and bitvecs. No integers, let alone reals and arrays and tuples and whatever.

However, it can serve as education tool (hopefully).

It parses input SMT-LIB file (see "tests" and "examples"), constructs digital circuit, which is then converted to CNF form using Tseitin transformations.
This is also called "bitblasting".
minisat is then executed, as an external SAT solver.

Stay tuned, it will be evolved.

Aside from SMT-LIB standard, I also added two more commands: (get-all-models) and (count-models) (see "tests").

Requires: flex/bison, boehm gc.
In Ubuntu Linux, type "make".
I wasn't checked on other OS-es.

