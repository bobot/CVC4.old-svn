(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v3 BitVec[4]))
:extrafuns ((v0 BitVec[4]))
:extrafuns ((v1 BitVec[4]))
:extrafuns ((v2 BitVec[4]))
:extrafuns ((v4 BitVec[4]))
:status unknown
:formula
(flet ($n1 true)
(let (?n2 bv12[4])
(flet ($n3 (bvuge ?n2 v2))
(flet ($n4 (not $n3))
(flet ($n5 false)
(let (?n6 bv0[4])
(let (?n7 (bvnot v0))
(let (?n8 (bvlshr v1 ?n7))
(let (?n9 (bvneg ?n8))
(flet ($n10 (= ?n6 ?n9))
(flet ($n11 (not $n10))
(flet ($n12 (or $n5 $n10 $n11))
(let (?n13 (bvnot v2))
(let (?n14 (bvcomp ?n2 v0))
(let (?n15 (zero_extend[3] ?n14))
(let (?n16 (bvxnor ?n13 ?n15))
(flet ($n17 (distinct v2 ?n16))
(let (?n18 bv1[1])
(flet ($n19 (bvsgt v0 ?n13))
(let (?n20 bv0[1])
(let (?n21 (ite $n19 ?n18 ?n20))
(flet ($n22 (= ?n18 ?n21))
(flet ($n23 (bvsge v1 ?n6))
(let (?n24 (ite $n23 ?n18 ?n20))
(let (?n25 (zero_extend[3] ?n24))
(let (?n26 (ite $n22 ?n25 ?n13))
(flet ($n27 (bvsge ?n8 ?n26))
(flet ($n28 (not $n27))
(flet ($n29 (or $n5 $n17 $n28))
(flet ($n30 (bvule ?n2 ?n9))
(let (?n31 (ite $n30 ?n18 ?n20))
(let (?n32 (sign_extend[3] ?n31))
(flet ($n33 (bvsle ?n32 ?n16))
(flet ($n34 (not $n33))
(let (?n35 (bvxor v0 v4))
(flet ($n36 (bvugt ?n8 ?n35))
(let (?n37 (bvneg ?n13))
(flet ($n38 (bvslt ?n37 v4))
(let (?n39 (ite $n38 ?n18 ?n20))
(flet ($n40 (distinct ?n24 ?n39))
(let (?n41 (bvlshr ?n8 v3))
(flet ($n42 (bvslt ?n41 ?n9))
(flet ($n43 (or $n5 $n40 $n42))
(flet ($n44 (bvsle ?n7 ?n13))
(flet ($n45 (bvsle ?n6 ?n41))
(flet ($n46 (or $n5 $n44 $n45))
(flet ($n47 (and $n4 $n12 $n29 $n34 $n36 $n43 $n46))
$n47
))))))))))))))))))))))))))))))))))))))))))))))))
