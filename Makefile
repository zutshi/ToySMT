all: ToySMT

ToySMT: lex.yy.o y.tab.o ToySMT.o utils.o
	gcc ToySMT.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -g -o ToySMT

utils.o: utils.c utils.h
	gcc -Wall -c utils.c -g

lex.yy.c: smt2.l y.tab.h
	flex smt2.l
	#flex -d smt2.l

lex.yy.o: lex.yy.c
	gcc -Wall -c -DYYDEBUG=1 lex.yy.c -g

y.tab.h: smt2.y
	bison -y -d -t smt2.y

y.tab.o: y.tab.c y.tab.h
	gcc -Wall -c -DYYDEBUG=1 y.tab.c -g

ToySMT.o: ToySMT.c
	gcc -Wall -c ToySMT.c -g

clean:
	rm *.o
	rm lex.yy.c
	rm y.tab.c
	rm y.tab.h

