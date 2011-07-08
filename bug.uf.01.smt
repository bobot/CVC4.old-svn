(benchmark fuzzsmt
:logic QF_UF
:extrasorts (S1)
:extrasorts (S0)
:extrapreds ((p4 S1 S0))
:extrafuns ((f4 S0 S0))
:extrafuns ((v0 S0))
:extrafuns ((v2 S0))
:extrapreds ((p0 S0))
:extrafuns ((v3 S1))
:extrapreds ((p1 S1))
:extrafuns ((v5 S1))
:extrapreds ((p3 S0 S0 S0))
:extrafuns ((v1 S0))
:status unknown
:formula
(let (?n1 (f4 v2))
(let (?n2 (f4 v0))
(flet ($n3 (p3 ?n1 v1 ?n2))
(let (?n4 (ite $n3 v5 v3))
(flet ($n5 (p1 ?n4))
(flet ($n6 (p0 ?n2))
(flet ($n7 (distinct ?n1 v0))
(let (?n8 (ite $n7 ?n1 ?n2))
(let (?n9 (ite $n6 v0 ?n8))
(flet ($n10 (p4 v3 ?n9))
(flet ($n11 (xor $n5 $n10))
$n11
))))))))))))