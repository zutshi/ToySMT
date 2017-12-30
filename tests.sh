#!/usr/bin/env bash

./ToySMT tests/alloc_two_vars.smt > tmp && diff tmp tests/alloc_two_vars.correct
./ToySMT tests/bool1.smt > tmp && diff tmp tests/bool1.correct
./ToySMT tests/bool2.smt > tmp && diff tmp tests/bool2.correct
./ToySMT tests/bvadd_test.smt > tmp && diff tmp tests/bvadd_test.correct
./ToySMT tests/bvadd_test2.smt > tmp && diff tmp tests/bvadd_test2.correct
./ToySMT tests/bvneg_fixpoints.smt > tmp && diff tmp tests/bvneg_fixpoints.correct
./ToySMT tests/bvnot_test.smt > tmp && diff tmp tests/bvnot_test.correct
./ToySMT tests/DeMorgan1.smt > tmp && diff tmp tests/DeMorgan1.correct
./ToySMT tests/DeMorgan2.smt > tmp && diff tmp tests/DeMorgan2.correct
./ToySMT tests/bvsub_test.smt > tmp && diff tmp tests/bvsub_test.correct
./ToySMT tests/bvsub_3_args.smt > tmp && diff tmp tests/bvsub_3_args.correct
./ToySMT tests/bvugt_bvult_test.smt > tmp && diff tmp tests/bvugt_bvult_test.correct
./ToySMT tests/bvugt_bvult_test2.smt > tmp && diff tmp tests/bvugt_bvult_test2.correct
./ToySMT tests/bvuge_bvule_test.smt > tmp && diff tmp tests/bvuge_bvule_test.correct
./ToySMT tests/bvsub_1_arg.smt > tmp && diff tmp tests/bvsub_1_arg.correct

./ToySMT tests/distinct1.smt > tmp
a=$(cat tmp | grep bv | cut -d ';' -f 2 | sort | uniq | wc -l)
	
if [[ $a != "4" ]];
then
	echo "distinct1 failed"
	echo "got" $a
fi

./ToySMT tests/distinct2.smt > tmp && diff tmp tests/distinct2.correct
./ToySMT tests/distinct3.smt > tmp && diff tmp tests/distinct3.correct
./ToySMT tests/zero_extend_test.smt > tmp && diff tmp tests/zero_extend_test.correct
./ToySMT tests/extract_test.smt > tmp && diff tmp tests/extract_test.correct
./ToySMT tests/ite_test1.smt > tmp && diff tmp tests/ite_test1.correct
./ToySMT tests/bvmul_test.smt > tmp && diff tmp tests/bvmul_test.correct
./ToySMT tests/bvmul_test3.smt > tmp && diff tmp tests/bvmul_test3.correct
./ToySMT tests/factorize.smt > tmp && diff tmp tests/factorize.correct
./ToySMT tests/bvsubge.smt > tmp && diff tmp tests/bvsubge.correct
./ToySMT tests/bvudiv_test.smt > tmp && diff tmp tests/bvudiv_test.correct
./ToySMT tests/bvudiv_test2.smt > tmp && diff tmp tests/bvudiv_test2.correct
./ToySMT tests/bvneg_test.smt > tmp && diff tmp tests/bvneg_test.correct
./ToySMT tests/t1.smt > tmp && diff tmp tests/t1.correct
./ToySMT tests/XOR_alter.smt > tmp && diff tmp tests/XOR_alter.correct
./ToySMT tests/modinv.smt > tmp && diff tmp tests/modinv.correct
./ToySMT tests/bvneg_count_fixpoints.smt > tmp && diff tmp tests/bvneg_count_fixpoints.correct

