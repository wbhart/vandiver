all:
	gcc -O2 -Wall vandiver.c -o vandiver -I/home/wbhart/flint2 -I/home/wbhart/mpir-git -I/home/wbhart/mpfr-3.1.1 -L/home/wbhart/flint2 -L/home/wbhart/mpir-git/.libs -L/home/wbhart/mpfr-3.1.1/src/.libs -lmpir -lmpfr -lflint

	gcc -O2 -Wall cyclotomic.c -o cyclotomic -I/home/wbhart/flint2 -I/home/wbhart/mpir-git -I/home/wbhart/mpfr-3.1.1 -L/home/wbhart/flint2 -L/home/wbhart/mpir-git/.libs -L/home/wbhart/mpfr-3.1.1/src/.libs -lmpir -lmpfr -lflint

