(benchmark irit
:logic QF_LRA
:status sat
:extrafuns ((y Real))
:extrafuns ((v2 Real))
:formula
 (and
  (= 0 y)
  (ite true (= v2 y) (= v2 0))
 )
)
