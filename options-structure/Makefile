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

t_options.cc: t_options opt_template.cc
	../src/util/mkoptions opt_template.cc t_options >$@
u_options.cc: u_options opt_template.cc
	../src/util/mkoptions opt_template.cc u_options >$@
t_options.h: t_options opt_template.h
	../src/util/mkoptions opt_template.h t_options >$@
u_options.h: u_options opt_template.h
	../src/util/mkoptions opt_template.h u_options >$@
options_holder.h: t_options u_options options_holder_template.h
	../src/util/mkoptions options_holder_template.h t_options u_options >$@

include .deps
.deps: *.cc *.h t_options.cc u_options.cc t_options.h u_options.h options_holder.h
	g++ -MM *.cc > .deps

