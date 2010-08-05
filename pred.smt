(benchmark euf_simp1.smt
:status sat
:logic QF_UF
:category { crafted }

:extrafuns ((x U))
:extrafuns ((y U))
:extrafuns ((z U))
:extrafuns ((f U U))
:extrafuns ((g U U))
:extrafuns ((H U U U))
:extrafuns ((J U U U))



:formula
(and
 (f x)
 (= (f x) (f y))
 (not (f y))
)
)
