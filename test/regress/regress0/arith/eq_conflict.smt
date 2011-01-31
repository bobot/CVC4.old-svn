(benchmark eq_conflict
:logic QF_LRA
:extrafuns ((x_1 Real))
:status unsat
:formula
(flet ($n2 (= 2 x_1))
(flet ($n4 (= 0 x_1))
(flet ($n5 (and $n2 $n4))
$n5
))))
