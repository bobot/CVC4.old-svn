
(benchmark euf_simp3.smt
:status unsat
:logic QF_UF
:category { crafted }

:extrafuns ((x U))
:extrafuns ((y U))
:extrafuns ((z U))
:extrafuns ((f U U))

:formula
(and
 (or (= x y) (= x z))
 (not 
   (or (= (f x) (f y)) (= (f x) (f z)))
 )
)

)