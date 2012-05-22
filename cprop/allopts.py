
#try me: python allopts.py ~/benchmarks/smtlib2/QF_LRA/tta_startup/simple_startup_6nodes.abstract.induct.smt2 &> res ; grep "running\|user\|THEORY_ARITH\|sat/unsat" res > sel

import sys
from subprocess import Popen, PIPE, STDOUT
import multiprocessing
import itertools
import string

print sys.argv

assert len(sys.argv) > 1

binary = "/home/taking/ws/cvc4/branches/arithmetic/cprop/builds/bin/cvc4"
processes = 3

examples = sys.argv[1:]
optionsChoices = itertools.product(
    ["time"],
    [binary],
    ["--stats"],
    ["--disable-arith-rewrite-equalities",
     "--enable-arith-rewrite-equalities"],
    ["--arith-prop=none",
     "--arith-prop=new",
     "--arith-prop=old",
     "--arith-prop=both"],
    ["--unate-lemmas all",
     "--unate-lemmas none",
     "--unate-lemmas ineqs",
     "--unate-lemmas eqs"])

options = [string.join(o) for o in optionsChoices ]

runChoices = itertools.product(options, examples)
runs = [string.join(r) for r in runChoices ]

print options
print runs

def runCommandline(run):
    output = "running: " + run + "\n"
    p = Popen(run, shell=True, stdin=PIPE, stdout=PIPE, stderr=STDOUT, close_fds=True)
    output += p.stdout.read()
    return output

p = multiprocessing.Pool(processes)
res = p.map(runCommandline, runs)

for r in res:
    print r
