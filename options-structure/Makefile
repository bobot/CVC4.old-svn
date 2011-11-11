CC = $(CXX)

main: main.o options.o u.o u_opt.o t_opt.o

.PHONY: clean
clean:; rm -f *.o main .deps

t_opt.cc: t_options opt_template.cc
	../../src/util/mkoptions opt_template.cc t_options >$@
u_opt.cc: u_options opt_template.cc
	../../src/util/mkoptions opt_template.cc u_options >$@
t_opt.h: t_options opt_template.h
	../../src/util/mkoptions opt_template.h t_options >$@
u_opt.h: u_options opt_template.h
	../../src/util/mkoptions opt_template.h u_options >$@

include .deps
.deps: *.cc *.h
	g++ -MM *.cc > .deps

