./ToySMT tests/alloc_two_vars.smt > tmp && diff tmp tests/alloc_two_vars.correct
./ToySMT tests/bool1.smt > tmp && diff tmp tests/bool1.correct
./ToySMT tests/bool2.smt > tmp && diff tmp tests/bool2.correct
./ToySMT tests/bvadd_test.smt > tmp && diff tmp tests/bvadd_test.correct
./ToySMT tests/bvneg_fixpoints.smt > tmp && diff tmp tests/bvneg_fixpoints.correct
./ToySMT tests/bvnot_test.smt > tmp && diff tmp tests/bvnot_test.correct
./ToySMT tests/DeMorgan1.smt > tmp && diff tmp tests/DeMorgan1.correct
./ToySMT tests/DeMorgan2.smt > tmp && diff tmp tests/DeMorgan2.correct

