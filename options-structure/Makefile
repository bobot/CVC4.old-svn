CC = $(CXX)

main: main.o options.o u.o u_opt.o t_opt.o

.PHONY: clean
clean:; rm -f *.o main .deps

include .deps
.deps: *.cc *.h
	g++ -MM *.cc > .deps

