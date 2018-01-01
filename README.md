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
It wasn't checked on other OS-es.

Since it's early preview, it was only checked on "tests" and "examples" you can find here.
Anything else can fail.
Also, error reporting is somewhat user-unfriendly.
First, you can check your .smt files using other SMT solver (I used z3, Boolector, STP, Yices, CVC4).

## Naming

ToySMT is not to be confused with this project: https://github.com/msakai/toysolver
Perhaps, I should find another name...

Any suggestions?

Since other SMT-solvers use cryptic acronyms as names, and since the name of Z3 has probably been taken from Z3 computer,
I'm considering name "RK86" ( after Soviet DIY home computer [Radio-86RK](https://en.wikipedia.org/wiki/Radio-86RK) )
and "MK85" ( after Soviet programmable calculator [Elektronika MK-85](http://www.leningrad.su/museum/show_calc.php?n=224) ).

## History

I've written many SAT examples in Python, based on this library (or API):
https://github.com/DennisYurichev/SAT_SMT_article/blob/master/libs/Xu.py
Many SAT Python-based examples has been published in my blog: https://yurichev.com/blog/

And at some point I realised I can do simple SMT-solver, I need only to add parser and keep tabs on variables.
This is what I did.

## Extreme simplicity

It has no optimizations at all.
If it encounters two "(bvadd x y)", two adders would be generated instead of one.
Maybe SAT-solver (minisat in this case) could optimize this out, or maybe not.

