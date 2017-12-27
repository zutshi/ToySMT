COPT=-Wall -g -c -O3
#COPT=-Wall -g -pg -c

all: ToySMT

ToySMT: lex.yy.o y.tab.o ToySMT.o utils.o
	#gcc ToySMT.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -lgc -g -pg -o ToySMT
	gcc ToySMT.o y.tab.o lex.yy.o utils.o -L/usr/local/lib/ -lgc -g -o ToySMT

utils.o: utils.c utils.h
	gcc $(COPT) utils.c

lex.yy.c: smt2.l y.tab.h
	flex smt2.l
	#flex -d smt2.l

lex.yy.o: lex.yy.c
	gcc $(COPT) -DYYDEBUG=1 lex.yy.c

y.tab.h: smt2.y
	bison -y -d -t smt2.y

y.tab.o: y.tab.c y.tab.h
	gcc $(COPT) -DYYDEBUG=1 y.tab.c

ToySMT.o: ToySMT.c
	gcc $(COPT) ToySMT.c

clean:
	rm *.o
	rm lex.yy.c
	rm y.tab.c
	rm y.tab.h

