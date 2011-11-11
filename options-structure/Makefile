CC = $(CXX)

main: main.o options.o u.o u_opt_internal.o t_opt_internal.o

.PHONY: clean
clean:; rm -f *.o main .deps

include .deps
.deps: *.cc *.h
	g++ -MM *.cc > .deps

