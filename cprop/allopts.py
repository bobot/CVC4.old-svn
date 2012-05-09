
#try me: python allopts.py ~/benchmarks/smtlib2/QF_LRA/tta_startup/simple_startup_6nodes.abstract.induct.smt2 &> res ; grep "running\|user\|THEORY_ARITH\|sat/unsat" res > sel

import sys
import subprocess
import itertools
import string

print sys.argv

assert len(sys.argv) > 1

examples = sys.argv[1:]
optionsChoices = itertools.product(
    ["--unate-lemmas all",
     "--unate-lemmas none",
     "--unate-lemmas ineqs",
     "--unate-lemmas eqs"],
    ["",
     "--disable-arith-rewrite-equalities"])

options = [string.join(o) for o in optionsChoices ]

print options

binary = "/home/taking/ws/cvc4/branches/arithmetic/cprop/builds/bin/cvc4"
fixedOptions = "--stats"
run = "time " + binary +" "+fixedOptions+" "

for e in examples:
    for opt in options:
        run = "time " + binary +" "+fixedOptions+" " + opt + " " + e
        print "running:", run
        sys.stdout.flush()
        subprocess.call(run, shell=True)
        sys.stdout.flush()
        sys.stderr.flush()
