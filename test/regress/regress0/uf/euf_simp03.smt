
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
 (not (= x (f (f x))))
 (= (f (f x)) (f (f (f x))))
 (= (f (f (f (f x)))) (f x))
 (not (= (f x) (f (f x))))
 )
)
