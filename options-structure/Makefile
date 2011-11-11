CC = $(CXX)

main: main.o options.o u.o u_options.o t_options.o
t_options.o: t_options.h t_options.cc
u_options.o: u_options.h u_options.cc
main.o: options_holder.h
t_options:
u_options:

.PHONY: clean
clean:
	rm -f *.o main .deps
	rm -f t_options.cc u_options.cc t_options.h u_options.h options_holder.h

include .deps
.deps: *.cc *.h
	g++ -MM *.cc > .deps

