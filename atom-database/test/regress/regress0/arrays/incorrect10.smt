(benchmark fuzzsmt
:logic QF_AX
:status unsat
:extrafuns ((v0 Array))
:extrafuns ((v1 Index))
:extrafuns ((v2 Index))
:extrafuns ((v3 Element))
:formula
(let (?e4 (store v0 v1 v3))
(let (?e5 (store ?e4 v2 v3))
(let (?e6 (select ?e5 v1))
(let (?e7 (select ?e4 v1))
(let (?e8 (select ?e4 v1))
(let (?e9 (store ?e4 v2 ?e8))
(let (?e10 (select ?e9 v1))
(let (?e11 (select ?e9 v1))
(flet ($e12 (= v0 v0))
(flet ($e13 (distinct ?e5 v0))
(flet ($e14 (= ?e5 ?e9))
(flet ($e15 (= v0 v0))
(flet ($e16 (= ?e5 ?e4))
(flet ($e17 (= v2 v1))
(flet ($e18 (= ?e10 ?e11))
(flet ($e19 (= v3 ?e6))
(flet ($e20 (= ?e6 ?e8))
(flet ($e21 (distinct ?e6 ?e11))
(flet ($e22 (= ?e11 ?e10))
(flet ($e23 (= ?e7 ?e6))
(let (?e24 (ite $e18 ?e4 ?e4))
(let (?e25 (ite $e16 ?e5 ?e24))
(let (?e26 (ite $e14 v0 ?e4))
(let (?e27 (ite $e17 ?e9 ?e26))
(let (?e28 (ite $e22 v0 v0))
(let (?e29 (ite $e20 ?e28 ?e28))
(let (?e30 (ite $e21 ?e27 ?e9))
(let (?e31 (ite $e14 ?e27 ?e4))
(let (?e32 (ite $e15 ?e27 ?e25))
(let (?e33 (ite $e13 ?e28 ?e4))
(let (?e34 (ite $e12 ?e33 ?e27))
(let (?e35 (ite $e23 ?e25 ?e9))
(let (?e36 (ite $e14 ?e9 ?e9))
(let (?e37 (ite $e15 ?e26 ?e5))
(let (?e38 (ite $e19 ?e26 ?e5))
(let (?e39 (ite $e15 v1 v2))
(let (?e40 (ite $e16 v2 ?e39))
(let (?e41 (ite $e18 ?e40 v1))
(let (?e42 (ite $e21 ?e39 v2))
(let (?e43 (ite $e17 v1 ?e39))
(let (?e44 (ite $e13 v1 v2))
(let (?e45 (ite $e22 ?e40 ?e42))
(let (?e46 (ite $e23 ?e41 v2))
(let (?e47 (ite $e12 ?e41 ?e39))
(let (?e48 (ite $e19 ?e47 ?e39))
(let (?e49 (ite $e18 v1 v2))
(let (?e50 (ite $e14 ?e43 ?e49))
(let (?e51 (ite $e20 ?e49 ?e46))
(let (?e52 (ite $e16 v3 v3))
(let (?e53 (ite $e17 ?e10 v3))
(let (?e54 (ite $e12 ?e6 ?e8))
(let (?e55 (ite $e12 ?e11 ?e10))
(let (?e56 (ite $e13 v3 ?e10))
(let (?e57 (ite $e15 ?e7 ?e54))
(let (?e58 (ite $e19 ?e10 ?e55))
(let (?e59 (ite $e18 ?e52 ?e7))
(let (?e60 (ite $e23 ?e56 ?e8))
(let (?e61 (ite $e14 ?e57 ?e59))
(let (?e62 (ite $e12 ?e55 v3))
(let (?e63 (ite $e22 ?e52 ?e11))
(let (?e64 (ite $e13 ?e61 v3))
(let (?e65 (ite $e20 ?e6 ?e63))
(let (?e66 (ite $e21 ?e11 ?e63))
(let (?e67 (store ?e28 ?e41 ?e66))
(let (?e68 (store v0 ?e42 ?e8))
(let (?e69 (select ?e27 ?e43))
(let (?e70 (select ?e35 ?e40))
(let (?e71 (select ?e28 ?e44))
(let (?e72 (store ?e25 ?e39 ?e65))
(let (?e73 (select ?e67 ?e45))
(let (?e74 (store ?e25 v1 ?e66))
(let (?e75 (select ?e34 ?e48))
(flet ($e76 (= ?e37 ?e33))
(flet ($e77 (distinct ?e34 ?e34))
(flet ($e78 (= ?e32 ?e30))
(flet ($e79 (distinct ?e31 ?e74))
(flet ($e80 (= ?e33 ?e26))
(flet ($e81 (= ?e31 ?e36))
(flet ($e82 (distinct ?e34 ?e9))
(flet ($e83 (distinct ?e9 ?e67))
(flet ($e84 (= ?e28 ?e27))
(flet ($e85 (distinct ?e33 ?e33))
(flet ($e86 (= v0 ?e68))
(flet ($e87 (distinct ?e29 ?e27))
(flet ($e88 (distinct ?e72 ?e4))
(flet ($e89 (distinct ?e37 ?e5))
(flet ($e90 (= ?e67 ?e38))
(flet ($e91 (distinct ?e27 ?e67))
(flet ($e92 (distinct ?e30 ?e25))
(flet ($e93 (distinct ?e33 ?e38))
(flet ($e94 (= ?e30 ?e25))
(flet ($e95 (distinct ?e5 ?e37))
(flet ($e96 (distinct ?e37 ?e35))
(flet ($e97 (distinct ?e38 ?e29))
(flet ($e98 (distinct ?e4 ?e4))
(flet ($e99 (distinct ?e25 ?e26))
(flet ($e100 (= ?e32 ?e24))
(flet ($e101 (= ?e40 ?e46))
(flet ($e102 (distinct ?e51 ?e47))
(flet ($e103 (= ?e51 ?e47))
(flet ($e104 (= ?e46 ?e51))
(flet ($e105 (= ?e41 ?e41))
(flet ($e106 (distinct ?e43 ?e41))
(flet ($e107 (distinct ?e49 ?e42))
(flet ($e108 (distinct ?e44 ?e46))
(flet ($e109 (distinct ?e45 ?e49))
(flet ($e110 (= ?e50 ?e43))
(flet ($e111 (= ?e51 ?e39))
(flet ($e112 (= ?e45 ?e47))
(flet ($e113 (= ?e41 v2))
(flet ($e114 (= ?e51 ?e50))
(flet ($e115 (distinct ?e45 ?e46))
(flet ($e116 (distinct v2 ?e47))
(flet ($e117 (= ?e45 ?e44))
(flet ($e118 (distinct ?e41 ?e51))
(flet ($e119 (= ?e46 ?e49))
(flet ($e120 (distinct ?e50 ?e41))
(flet ($e121 (= ?e50 ?e49))
(flet ($e122 (distinct ?e50 ?e50))
(flet ($e123 (distinct ?e41 ?e48))
(flet ($e124 (distinct ?e46 ?e46))
(flet ($e125 (= ?e39 v1))
(flet ($e126 (distinct ?e6 ?e71))
(flet ($e127 (= ?e58 ?e61))
(flet ($e128 (= ?e7 ?e58))
(flet ($e129 (distinct ?e66 ?e71))
(flet ($e130 (= ?e7 ?e63))
(flet ($e131 (= ?e53 ?e59))
(flet ($e132 (distinct ?e63 ?e55))
(flet ($e133 (= ?e66 ?e7))
(flet ($e134 (distinct ?e60 ?e53))
(flet ($e135 (distinct ?e52 ?e65))
(flet ($e136 (distinct ?e11 ?e11))
(flet ($e137 (= ?e54 ?e57))
(flet ($e138 (= ?e73 v3))
(flet ($e139 (= ?e70 ?e66))
(flet ($e140 (distinct ?e59 ?e61))
(flet ($e141 (distinct ?e7 ?e54))
(flet ($e142 (= ?e70 ?e73))
(flet ($e143 (distinct v3 ?e10))
(flet ($e144 (= ?e7 ?e58))
(flet ($e145 (= ?e57 ?e69))
(flet ($e146 (distinct ?e52 ?e58))
(flet ($e147 (distinct ?e55 ?e62))
(flet ($e148 (= ?e10 ?e66))
(flet ($e149 (distinct ?e70 ?e75))
(flet ($e150 (= v3 ?e60))
(flet ($e151 (= ?e7 ?e52))
(flet ($e152 (distinct ?e73 ?e64))
(flet ($e153 (= ?e56 ?e57))
(flet ($e154 (distinct ?e52 ?e75))
(flet ($e155 (distinct ?e66 ?e69))
(flet ($e156 (= ?e56 ?e63))
(flet ($e157 (= ?e11 ?e10))
(flet ($e158 (= ?e69 ?e65))
(flet ($e159 (distinct ?e52 ?e7))
(flet ($e160 (= ?e53 ?e8))
(flet ($e161 (implies $e83 $e151))
(flet ($e162 (and $e156 $e109))
(flet ($e163 (not $e133))
(flet ($e164 (implies $e100 $e143))
(flet ($e165 (iff $e114 $e162))
(flet ($e166 (or $e76 $e152))
(flet ($e167 (and $e12 $e93))
(flet ($e168 (xor $e164 $e78))
(flet ($e169 (and $e15 $e106))
(flet ($e170 (not $e111))
(flet ($e171 (xor $e18 $e135))
(flet ($e172 (not $e14))
(flet ($e173 (iff $e125 $e20))
(flet ($e174 (iff $e84 $e142))
(flet ($e175 (if_then_else $e129 $e150 $e153))
(flet ($e176 (iff $e80 $e118))
(flet ($e177 (xor $e99 $e103))
(flet ($e178 (or $e97 $e91))
(flet ($e179 (if_then_else $e127 $e77 $e172))
(flet ($e180 (and $e169 $e101))
(flet ($e181 (or $e147 $e90))
(flet ($e182 (implies $e181 $e157))
(flet ($e183 (or $e94 $e119))
(flet ($e184 (and $e120 $e174))
(flet ($e185 (iff $e23 $e177))
(flet ($e186 (or $e86 $e85))
(flet ($e187 (implies $e132 $e16))
(flet ($e188 (if_then_else $e187 $e186 $e21))
(flet ($e189 (or $e92 $e92))
(flet ($e190 (xor $e113 $e128))
(flet ($e191 (iff $e179 $e171))
(flet ($e192 (not $e104))
(flet ($e193 (and $e137 $e107))
(flet ($e194 (or $e170 $e176))
(flet ($e195 (or $e134 $e188))
(flet ($e196 (and $e112 $e116))
(flet ($e197 (if_then_else $e122 $e163 $e17))
(flet ($e198 (if_then_else $e102 $e87 $e13))
(flet ($e199 (or $e184 $e197))
(flet ($e200 (implies $e189 $e196))
(flet ($e201 (and $e191 $e79))
(flet ($e202 (iff $e145 $e124))
(flet ($e203 (if_then_else $e139 $e199 $e182))
(flet ($e204 (iff $e146 $e141))
(flet ($e205 (iff $e98 $e175))
(flet ($e206 (or $e190 $e148))
(flet ($e207 (and $e159 $e185))
(flet ($e208 (xor $e144 $e165))
(flet ($e209 (if_then_else $e202 $e167 $e19))
(flet ($e210 (or $e208 $e180))
(flet ($e211 (or $e89 $e203))
(flet ($e212 (not $e198))
(flet ($e213 (iff $e210 $e211))
(flet ($e214 (implies $e205 $e81))
(flet ($e215 (not $e192))
(flet ($e216 (or $e110 $e213))
(flet ($e217 (implies $e96 $e154))
(flet ($e218 (not $e155))
(flet ($e219 (xor $e136 $e105))
(flet ($e220 (iff $e217 $e130))
(flet ($e221 (or $e138 $e126))
(flet ($e222 (not $e178))
(flet ($e223 (if_then_else $e215 $e82 $e140))
(flet ($e224 (not $e221))
(flet ($e225 (implies $e204 $e220))
(flet ($e226 (xor $e168 $e209))
(flet ($e227 (or $e95 $e214))
(flet ($e228 (implies $e218 $e218))
(flet ($e229 (not $e225))
(flet ($e230 (not $e229))
(flet ($e231 (implies $e222 $e228))
(flet ($e232 (and $e226 $e121))
(flet ($e233 (iff $e206 $e108))
(flet ($e234 (and $e230 $e166))
(flet ($e235 (implies $e231 $e232))
(flet ($e236 (not $e88))
(flet ($e237 (not $e201))
(flet ($e238 (if_then_else $e237 $e236 $e173))
(flet ($e239 (and $e235 $e193))
(flet ($e240 (xor $e239 $e238))
(flet ($e241 (implies $e123 $e219))
(flet ($e242 (if_then_else $e234 $e212 $e149))
(flet ($e243 (or $e115 $e242))
(flet ($e244 (and $e200 $e183))
(flet ($e245 (implies $e207 $e233))
(flet ($e246 (iff $e22 $e241))
(flet ($e247 (implies $e194 $e240))
(flet ($e248 (implies $e223 $e131))
(flet ($e249 (or $e227 $e158))
(flet ($e250 (and $e160 $e224))
(flet ($e251 (or $e250 $e243))
(flet ($e252 (or $e117 $e117))
(flet ($e253 (and $e195 $e248))
(flet ($e254 (xor $e253 $e249))
(flet ($e255 (implies $e246 $e254))
(flet ($e256 (iff $e251 $e161))
(flet ($e257 (xor $e216 $e245))
(flet ($e258 (xor $e255 $e256))
(flet ($e259 (iff $e244 $e257))
(flet ($e260 (if_then_else $e247 $e259 $e247))
(flet ($e261 (xor $e258 $e252))
(flet ($e262 (not $e260))
(flet ($e263 (or $e262 $e262))
(flet ($e264 (iff $e263 $e263))
(flet ($e265 (and $e261 $e261))
(flet ($e266 (implies $e264 $e264))
(flet ($e267 (and $e265 $e266))
$e267
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
