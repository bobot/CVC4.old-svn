(benchmark delta_tta_startup
:logic QF_LRA
:extrafuns ((x_3 Real))
:extrafuns ((x_4 Real))
:extrafuns ((x_6 Real))
:extrafuns ((x_31 Real))
:status sat
:formula
(and (<= x_3 x_4)
     (or (= 1 x_31) true)
     (or (>= x_3 x_4) (= x_4 x_6))
     (or true (= x_3 x_4))
     (> x_6 x_4)
)

)
