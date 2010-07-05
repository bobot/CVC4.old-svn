(benchmark synch_circuit
:logic QF_LRA
:extrafuns ((x_100 Real))
:extrafuns ((x_74 Real))
:extrafuns ((x_92 Real))
:status unsat
:formula
(flet ($n1 (= x_92 x_100))
(flet ($n2 (not $n1))
(flet ($n3 (= x_74 x_92))
(flet ($n4 (= x_74 x_100))
(flet ($n5 (and $n3 $n4))
(flet ($n6 (and $n2 $n5))
$n6
)))))))
