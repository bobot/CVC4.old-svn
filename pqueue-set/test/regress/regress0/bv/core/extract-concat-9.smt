(benchmark B_
  :logic QF_BV
  :status unsat
  :extrafuns ((x BitVec[32]))
  :extrafuns ((y BitVec[32]))
  :formula
(not (= (extract[61:2] (concat x y)) (concat (extract[29:0] x) (extract[31:2] y))))
)
