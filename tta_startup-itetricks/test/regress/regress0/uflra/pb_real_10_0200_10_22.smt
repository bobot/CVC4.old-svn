(benchmark mathsat
:source { MathSat group }
:logic QF_UFLRA
:status unsat 
:category { random } 
:difficulty { 3 }
:extrafuns ((f0_1 Real Real))
:extrafuns ((f0_2 Real Real Real))
:extrafuns ((f0_3 Real Real Real Real))
:extrafuns ((f0_4 Real Real Real Real Real))
:extrafuns ((f1_1 Real Real))
:extrafuns ((f1_2 Real Real Real))
:extrafuns ((f1_3 Real Real Real Real))
:extrafuns ((f1_4 Real Real Real Real Real))
:extrafuns ((x0 Real))
:extrafuns ((x1 Real))
:extrafuns ((x2 Real))
:extrafuns ((x3 Real))
:extrafuns ((x4 Real))
:extrafuns ((x5 Real))
:extrafuns ((x6 Real))
:extrafuns ((x7 Real))
:extrafuns ((x8 Real))
:extrafuns ((x9 Real))
:extrapreds ((P0))
:extrapreds ((P1))
:extrapreds ((P2))
:extrapreds ((P3))
:extrapreds ((P4))
:extrapreds ((P5))
:extrapreds ((P6))
:extrapreds ((P7))
:extrapreds ((P8))
:extrapreds ((P9))
:formula
(let (?x10 (f0_1 x3))
(let (?x11 (f0_1 x4))
(let (?x12 (f1_2 x7 x0))
(let (?x13 (- (- (* (- 0 11) x9) (* 21 x4)) (* 11 x7)))
(let (?x14 (- (+ (* 26 x3) (* 17 x5)) (* 1 x6)))
(let (?x15 (- (+ (* 18 x2) (* 9 x9)) (* 7 x6)))
(let (?x16 (- (- (* 24 x6) (* 9 x9)) (* 13 x5)))
(let (?x17 (+ (- (* 13 x0) (* 15 x3)) (* 6 x2)))
(let (?x18 (f0_1 x6))
(let (?x19 (f0_2 x1 x6))
(let (?x20 (- (+ (* 29 x6) (* 21 x7)) (* 25 x9)))
(let (?x21 (+ (+ (* (- 0 18) x6) (* 13 x5)) (* 2 x7)))
(let (?x22 (+ (+ (* 16 x0) (* 10 x1)) (* 15 x3)))
(let (?x23 (f1_2 x5 x0))
(let (?x24 (- (+ (* 2 x8) (* 27 x5)) (* 9 x0)))
(let (?x25 (- (+ (* (- 0 27) x1) (* 23 x9)) (* 22 x5)))
(let (?x26 (f0_2 ?x21 x6))
(let (?x27 (f1_1 x7))
(let (?x28 (f0_2 ?x14 ?x17))
(let (?x29 (- (+ (* 26 ?x10) (* 24 ?x26)) (* 6 x7)))
(let (?x30 (f0_2 x1 x0))
(let (?x31 (f1_2 x8 x5))
(let (?x32 (f1_1 ?x21))
(let (?x33 (f1_1 ?x14))
(let (?x34 (f0_2 x8 x7))
(let (?x35 (f0_2 ?x33 ?x31))
(let (?x36 (+ (- (* (- 0 13) x3) (* 8 x9)) (* 6 x4)))
(let (?x37 (- (- (* (- 0 9) x1) (* 22 x3)) (* 19 x8)))
(let (?x38 (f0_2 x2 x9))
(let (?x39 (f0_2 ?x13 ?x11))
(let (?x40 (f1_2 x0 x7))
(let (?x41 (f1_1 x2))
(let (?x42 (f0_1 x1))
(let (?x43 (f1_2 x7 x4))
(let (?x44 (+ (+ (* 7 x5) (* 15 x5)) (* 24 x0)))
(let (?x45 (+ (+ (* 27 x7) (* 22 x9)) (* 24 x6)))
(let (?x46 (f1_2 x8 x6))
(let (?x47 (+ (+ (* (- 0 24) x6) (* 13 x2)) (* 15 x7)))
(let (?x48 (f0_2 ?x26 ?x43))
(let (?x49 (+ (+ (* 15 x2) (* 6 x5)) (* 10 x9)))
(flet ($P10 (< ?x36 (- 0 5)))
(flet ($P11 (< ?x48 (- 0 26)))
(flet ($P12 (< ?x34 6))
(flet ($P13 (< ?x29 13))
(flet ($P14 (< ?x17 20))
(flet ($P15 (< x4 (- 0 27)))
(flet ($P16 (< ?x39 (- 0 11)))
(flet ($P17 (< ?x49 (- 0 25)))
(flet ($P18 (< ?x11 10))
(flet ($P19 (< ?x35 (- 0 28)))
(flet ($P20 (< x6 6))
(flet ($P21 (< ?x37 10))
(flet ($P22 (< ?x25 9))
(flet ($P23 (< ?x29 (- 0 5)))
(flet ($P24 (< ?x44 (- 0 25)))
(flet ($P25 (< ?x25 28))
(flet ($P26 (< x5 (- 0 12)))
(flet ($P27 (< ?x45 16))
(flet ($P28 (= ?x22 ?x10))
(flet ($P29 (< x5 14))
(flet ($P30 (= ?x14 ?x14))
(flet ($P31 (< ?x31 15))
(flet ($P32 (= ?x12 ?x17))
(flet ($P33 (< ?x45 (- 0 6)))
(flet ($P34 (< ?x27 (- 0 25)))
(flet ($P35 (= ?x46 ?x13))
(flet ($P36 (= ?x33 ?x48))
(flet ($P37 (< ?x49 (- 0 23)))
(flet ($P38 (= ?x29 ?x45))
(flet ($P39 (< ?x14 (- 0 20)))
(flet ($P40 (< ?x37 12))
(flet ($P41 (< x1 (- 0 4)))
(flet ($P42 (< x1 29))
(flet ($P43 (< ?x29 8))
(flet ($P44 (< ?x20 (- 0 26)))
(flet ($P45 (< ?x23 0))
(flet ($P46 (= x4 ?x15))
(flet ($P47 (< ?x19 9))
(flet ($P48 (< ?x43 4))
(flet ($P49 (< ?x45 16))
(flet ($P50 (< ?x16 (- 0 8)))
(flet ($P51 (< ?x37 (- 0 18)))
(flet ($P52 (< ?x27 10))
(flet ($P53 (= ?x40 ?x30))
(flet ($P54 (< ?x20 26))
(flet ($P55 (< ?x34 11))
(flet ($P56 (= ?x39 ?x49))
(flet ($P57 (< ?x43 (- 0 22)))
(flet ($P58 (< ?x46 (- 0 3)))
(flet ($P59 (< x7 (- 0 22)))
(and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or (or (not P8) $P49) $P33) (or (or (not P2) $P55) (not $P51))) (or (or (not P8) $P17) (not $P28))) (or (or (not $P50) (not $P17)) (not $P39))) (or (or (not $P26) $P48) (not $P13))) (or (or $P55 (not $P31)) $P38)) (or (or $P30 $P17) (not $P11))) (or (or (not $P40) (not $P17)) $P24)) (or (or $P41 $P20) P4)) (or (or $P33 (not P7)) $P31)) (or (or P4 $P43) $P11)) (or (or $P25 P7) (not $P54))) (or (or (not $P11) (not $P59)) (not $P35))) (or (or (not $P54) (not $P54)) $P34)) (or (or $P46 $P48) (not $P43))) (or (or (not $P50) $P49) (not $P36))) (or (or (not $P50) $P25) (not $P54))) (or (or (not $P43) (not $P37)) (not $P38))) (or (or (not $P21) (not $P38)) $P29)) (or (or (not $P13) (not $P36)) $P11)) (or (or (not $P50) (not $P15)) $P23)) (or (or $P57 $P23) $P52)) (or (or $P27 $P44) (not $P30))) (or (or (not P8) (not $P46)) (not $P32))) (or (or (not $P51) (not $P49)) (not $P16))) (or (or (not $P35) (not $P12)) (not $P38))) (or (or (not $P28) $P37) (not $P20))) (or (or $P59 $P36) (not $P28))) (or (or (not $P58) (not $P43)) (not $P45))) (or (or (not $P32) (not $P58)) P3)) (or (or (not P5) (not $P58)) $P55)) (or (or $P51 $P53) (not $P18))) (or (or $P21 $P43) (not $P19))) (or (or (not $P26) (not $P55)) (not $P30))) (or (or $P46 $P40) $P55)) (or (or $P14 $P30) (not $P35))) (or (or P3 $P44) (not $P50))) (or (or $P46 (not $P33)) (not $P54))) (or (or (not $P44) $P53) (not $P20))) (or (or (not $P29) $P44) $P50)) (or (or (not $P48) (not $P19)) $P40)) (or (or (not $P49) P8) $P29)) (or (or $P58 (not P2)) $P37)) (or (or $P11 (not $P52)) P2)) (or (or $P43 $P50) (not $P37))) (or (or $P19 $P43) P0)) (or (or (not $P17) $P51) (not $P29))) (or (or P0 (not $P57)) (not $P11))) (or (or (not $P39) $P10) $P42)) (or (or (not $P14) (not $P42)) (not $P21))) (or (or $P43 P8) $P19)) (or (or (not $P21) P3) $P38)) (or (or P5 (not $P33)) (not $P10))) (or (or (not $P35) (not $P28)) $P44)) (or (or $P47 (not $P53)) $P20)) (or (or $P54 (not $P21)) (not $P23))) (or (or (not P0) (not $P35)) $P24)) (or (or $P35 $P45) (not P7))) (or (or (not $P54) (not $P46)) (not $P49))) (or (or (not $P55) $P21) $P43)) (or (or (not $P16) $P36) (not $P19))) (or (or (not P1) $P48) (not $P44))) (or (or (not $P10) $P54) $P43)) (or (or (not $P14) (not $P43)) $P18)) (or (or P0 $P43) $P38)) (or (or (not $P38) (not $P43)) (not $P46))) (or (or P0 (not $P19)) (not $P12))) (or (or $P14 $P56) $P58)) (or (or $P51 $P56) (not $P12))) (or (or $P59 $P34) (not $P26))) (or (or (not P4) $P50) $P42)) (or (or $P38 (not $P44)) $P58)) (or (or $P53 (not P1)) (not $P37))) (or (or (not P2) $P20) $P23)) (or (or P3 $P47) $P18)) (or (or $P49 (not $P11)) $P34)) (or (or (not $P38) $P34) $P21)) (or (or (not $P32) $P17) (not $P22))) (or (or (not $P13) $P29) $P58)) (or (or (not $P24) $P52) (not $P44))) (or (or (not $P16) $P30) (not $P38))) (or (or (not $P22) (not $P23)) (not $P31))) (or (or (not $P57) (not $P31)) $P18)) (or (or $P38 $P46) $P19)) (or (or $P38 $P23) (not $P24))) (or (or $P30 $P34) (not $P51))) (or (or (not $P50) $P42) (not $P41))) (or (or (not P7) (not $P37)) (not $P31))) (or (or (not $P42) $P38) (not $P27))) (or (or (not $P29) $P54) (not $P58))) (or (or $P44 $P18) $P21)) (or (or $P35 (not P4)) $P15)) (or (or $P14 $P38) $P17)) (or (or (not $P51) (not P4)) (not $P46))) (or (or (not $P50) $P16) (not $P27))) (or (or (not $P13) $P52) $P17)) (or (or (not $P57) (not $P24)) (not $P32))) (or (or (not $P12) $P14) (not P7))) (or (or $P39 $P28) (not $P25))) (or (or $P30 (not P4)) P8)) (or (or $P22 P9) (not $P59))) (or (or (not $P18) $P56) (not $P13))) (or (or $P20 (not $P32)) $P33)) (or (or (not $P23) $P52) P1)) (or (or $P11 (not $P20)) (not P9))) (or (or (not $P14) (not $P14)) $P59)) (or (or $P40 (not P9)) (not $P12))) (or (or (not $P14) (not $P33)) (not $P45))) (or (or (not $P17) (not P7)) (not $P54))) (or (or (not $P55) $P55) P5)) (or (or $P21 $P28) (not $P31))) (or (or $P50 $P26) $P20)) (or (or $P27 $P30) (not $P49))) (or (or P0 (not $P48)) $P58)) (or (or $P39 $P57) (not $P49))) (or (or (not $P20) $P28) (not $P10))) (or (or $P57 $P23) (not P1))) (or (or P5 $P25) $P11)) (or (or (not P8) (not $P47)) (not $P56))) (or (or $P26 (not P3)) (not $P27))) (or (or (not $P58) P5) (not P0))) (or (or $P12 P2) $P27)) (or (or $P22 $P58) (not $P57))) (or (or $P47 (not $P11)) $P33)) (or (or $P22 (not $P14)) $P13)) (or (or (not P0) (not $P23)) $P47)) (or (or (not $P50) $P15) (not $P32))) (or (or (not $P32) $P52) (not $P33))) (or (or (not $P58) $P46) $P26)) (or (or $P45 (not $P18)) (not $P26))) (or (or $P47 P6) (not $P37))) (or (or (not $P43) P1) (not $P36))) (or (or (not P0) (not $P49)) $P30)) (or (or (not $P59) (not P3)) (not $P52))) (or (or (not $P48) $P18) $P46)) (or (or (not P5) (not $P10)) $P43)) (or (or $P42 $P12) $P45)) (or (or $P57 (not $P18)) $P29)) (or (or $P41 P1) $P56)) (or (or (not $P43) (not $P16)) (not P2))) (or (or (not $P17) $P51) $P15)) (or (or $P31 (not $P23)) P7)) (or (or (not $P27) (not $P49)) (not P5))) (or (or (not $P13) $P57) (not $P56))) (or (or P7 P9) $P15)) (or (or (not $P54) $P52) (not $P17))) (or (or P8 (not $P35)) (not $P52))) (or (or $P25 (not $P16)) P5)) (or (or $P15 $P13) (not $P34))) (or (or (not P7) (not $P14)) $P22)) (or (or $P25 $P43) P3)) (or (or (not $P38) $P18) $P48)) (or (or P7 $P46) (not $P31))) (or (or (not $P47) (not $P16)) (not $P43))) (or (or P8 (not $P41)) P7)) (or (or (not $P35) (not P1)) (not P4))) (or (or $P56 $P48) $P26)) (or (or (not $P41) P3) (not $P53))) (or (or (not $P36) P1) (not $P56))) (or (or $P25 P1) $P23)) (or (or (not $P35) $P39) P9)) (or (or (not $P40) $P41) (not $P52))) (or (or (not $P34) (not $P13)) $P37)) (or (or P0 (not $P25)) (not P8))) (or (or (not $P31) (not $P41)) (not P8))) (or (or P7 P4) $P39)) (or (or (not $P33) (not $P39)) (not $P57))) (or (or $P24 (not $P13)) (not $P38))) (or (or $P58 $P29) P2)) (or (or (not $P50) (not $P38)) $P43)) (or (or (not $P44) $P37) $P11)) (or (or $P14 (not $P53)) (not $P47))) (or (or $P29 P2) (not $P24))) (or (or (not $P45) (not $P10)) $P50)) (or (or $P38 (not $P54)) (not $P18))) (or (or (not $P19) $P41) (not P4))) (or (or $P37 $P10) (not $P50))) (or (or (not $P48) $P41) $P47)) (or (or (not $P17) $P28) $P27)) (or (or (not $P17) (not $P35)) $P43)) (or (or (not $P24) $P12) $P11)) (or (or P5 (not $P24)) (not P1))) (or (or $P28 (not $P29)) (not P5))) (or (or (not $P30) (not $P22)) $P40)) (or (or (not $P47) P2) $P58)) (or (or $P22 (not $P26)) $P12)) (or (or (not $P38) (not $P59)) (not $P23))) (or (or (not P8) $P58) (not $P39))) (or (or $P51 $P41) $P21)) (or (or (not $P20) $P57) (not $P42))) (or (or $P38 $P17) (not $P52))) (or (or (not P1) $P25) (not $P58))) (or (or (not $P20) P2) $P47)) (or (or (not $P11) (not $P37)) (not $P33))) (or (or $P49 $P28) P7)) (or (or $P28 (not $P39)) $P45)) (or (or (not $P14) $P21) P8)) (or (or $P12 $P57) P5)) (or (or (not $P43) (not $P48)) $P46)) (or (or $P45 (not $P18)) $P28)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
