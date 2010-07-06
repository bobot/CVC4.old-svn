(benchmark pursuit_safety_13.smt
:logic QF_LRA
:extrafuns ((x_3 Real))
:extrafuns ((x_6 Real))
:extrafuns ((x_11 Real))
:extrafuns ((x_12 Real))
:extrafuns ((x_13 Real))
:extrafuns ((x_16 Real))
:extrafuns ((x_22 Real))
:extrafuns ((x_25 Real))
:extrafuns ((x_67 Real))
:extrafuns ((x_71 Real))
:extrafuns ((x_76 Real))
:extrafuns ((x_85 Real))
:extrafuns ((x_90 Real))



:status unsat
:formula
(and
     (= x_3 2)
     (= x_13 x_3)
     (= x_13 x_12)
     (= x_16 x_6)
     (= x_22 x_12)
     (= x_25 x_16)
     (not (= x_67 4))
     (< 1 (+ x_67 x_90))
     (= x_71 1)
     (= x_71 x_6)
     (= x_85 x_67)
     (= x_85 x_76)
     (= x_85 4)
)

)
