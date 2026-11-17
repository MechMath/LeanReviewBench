import Batteries.Data.Array.Lemmas
import Batteries.Tactic.Exact
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.TypeStar
import Qq
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EndToEnd.Certificate
import dep.equational_theories.EndToEnd.Dual
import dep.equational_theories.EndToEnd.Load
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.Equations.LawsComplete
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.FreeSemigroup
import dep.equational_theories.Generated.MagmaEgg.small._000
import dep.equational_theories.Generated.MagmaEgg.small._001
import dep.equational_theories.Generated.MagmaEgg.small._002
import dep.equational_theories.Generated.MagmaEgg.small._003
import dep.equational_theories.Generated.MagmaEgg.small._004
import dep.equational_theories.Generated.MagmaEgg.small._005
import dep.equational_theories.Generated.MagmaEgg.small._006
import dep.equational_theories.Generated.MagmaEgg.small._007
import dep.equational_theories.Generated.MagmaEgg.small._008
import dep.equational_theories.Generated.MagmaEgg.small._009
import dep.equational_theories.Generated.MagmaEgg.small._010
import dep.equational_theories.Generated.MagmaEgg.small._011
import dep.equational_theories.Generated.MagmaEgg.small._012
import dep.equational_theories.Generated.MagmaEgg.small._013
import dep.equational_theories.Generated.MagmaEgg.small._014
import dep.equational_theories.Generated.MagmaEgg.small._015
import dep.equational_theories.Generated.MagmaEgg.small._016
import dep.equational_theories.Generated.MagmaEgg.small._017
import dep.equational_theories.Generated.MagmaEgg.small._018
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.MemoFinOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray
import dep.equational_theories.Subgraph
import dep.equational_theories.Superposition

namespace EndToEnd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def _root_.EndToEnd.pos0 : RArray EndToEnd.PosFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 99, conc := 820, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 100, conc := 1030, proof := sorry })
                      (RArray.leaf { hyp := 102, conc := 1033, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 103, conc := 1257, proof := sorry })
                      (RArray.leaf { hyp := 105, conc := 840, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 108, conc := 850, proof := sorry })
                      (RArray.leaf { hyp := 9, conc := 109, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 109, conc := 1066, proof := sorry })
                      (RArray.leaf { hyp := 109, conc := 1269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 110, conc := 1067, proof := sorry })
                      (RArray.leaf { hyp := 111, conc := 1272, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 112, conc := 1070, proof := sorry })
                      (RArray.leaf { hyp := 112, conc := 1273, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 112, conc := 867, proof := sorry })
                      (RArray.leaf { hyp := 115, conc := 1757, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 118, conc := 887, proof := sorry })
                      (RArray.leaf { hyp := 10, conc := 3728, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 10, conc := 857, proof := sorry })
                      (RArray.leaf { hyp := 119, conc := 1103, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 119, conc := 1766, proof := sorry })
                      (RArray.leaf { hyp := 120, conc := 1104, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 121, conc := 1769, proof := sorry })
                      (RArray.leaf { hyp := 122, conc := 1107, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 122, conc := 1770, proof := sorry })
                      (RArray.leaf { hyp := 122, conc := 904, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 125, conc := 914, proof := sorry })
                      (RArray.leaf { hyp := 11, conc := 112, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 11, conc := 60, proof := sorry })
                      (RArray.leaf { hyp := 133, conc := 1399, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 134, conc := 1400, proof := sorry })
                      (RArray.leaf { hyp := 135, conc := 1808, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 136, conc := 1403, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 136, conc := 958, proof := sorry })
                      (RArray.leaf { hyp := 137, conc := 1404, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 12, conc := 185, proof := sorry })
                      (RArray.leaf { hyp := 140, conc := 1408, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 141, conc := 1820, proof := sorry })
                      (RArray.leaf { hyp := 145, conc := 1216, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 145, conc := 1419, proof := sorry })
                      (RArray.leaf { hyp := 145, conc := 1825, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 13, conc := 1557, proof := sorry })
                      (RArray.leaf { hyp := 13, conc := 3587, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 151, conc := 1429, proof := sorry })
                      (RArray.leaf { hyp := 152, conc := 1639, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 154, conc := 1642, proof := sorry })
                      (RArray.leaf { hyp := 155, conc := 1866, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 157, conc := 1869, proof := sorry })
                      (RArray.leaf { hyp := 14, conc := 188, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 14, conc := 70, proof := sorry })
                      (RArray.leaf { hyp := 160, conc := 1459, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 161, conc := 1675, proof := sorry })
                      (RArray.leaf { hyp := 162, conc := 1676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 163, conc := 1881, proof := sorry })
                      (RArray.leaf { hyp := 164, conc := 1476, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 164, conc := 1679, proof := sorry })
                      (RArray.leaf { hyp := 164, conc := 1882, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 165, conc := 2160, proof := sorry })
                      (RArray.leaf { hyp := 167, conc := 1486, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 15, conc := 1779, proof := sorry })
                      (RArray.leaf { hyp := 15, conc := 3413, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 172, conc := 1713, proof := sorry })
                      (RArray.leaf { hyp := 173, conc := 2175, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 174, conc := 1513, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 177, conc := 1523, proof := sorry })
                      (RArray.leaf { hyp := 181, conc := 1749, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 185, conc := 2008, proof := sorry })
                      (RArray.leaf { hyp := 187, conc := 2214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 188, conc := 2012, proof := sorry })
                      (RArray.leaf { hyp := 188, conc := 2215, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 189, conc := 2013, proof := sorry })
                      (RArray.leaf { hyp := 193, conc := 2226, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 197, conc := 2028, proof := sorry })
                      (RArray.leaf { hyp := 197, conc := 2231, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 18, conc := 145, proof := sorry })
                      (RArray.leaf { hyp := 18, conc := 197, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 204, conc := 2248, proof := sorry })
                      (RArray.leaf { hyp := 206, conc := 2251, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 207, conc := 2475, proof := sorry })
                      (RArray.leaf { hyp := 209, conc := 2478, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 212, conc := 1865, proof := sorry })
                      (RArray.leaf { hyp := 213, conc := 2284, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 213, conc := 2487, proof := sorry })
                      (RArray.leaf { hyp := 214, conc := 2285, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 215, conc := 2490, proof := sorry })
                      (RArray.leaf { hyp := 216, conc := 2288, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 216, conc := 2491, proof := sorry })
                      (RArray.leaf { hyp := 217, conc := 2769, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 219, conc := 2772, proof := sorry })
                      (RArray.leaf { hyp := 222, conc := 1902, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 223, conc := 2321, proof := sorry })
                      (RArray.leaf { hyp := 223, conc := 2781, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 224, conc := 2322, proof := sorry })
                      (RArray.leaf { hyp := 225, conc := 2784, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 226, conc := 1919, proof := sorry })
                      (RArray.leaf { hyp := 226, conc := 2325, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 226, conc := 2785, proof := sorry })
                      (RArray.leaf { hyp := 229, conc := 1929, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 233, conc := 2358, proof := sorry })
                      (RArray.leaf { hyp := 236, conc := 2362, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 237, conc := 2617, proof := sorry })
                      (RArray.leaf { hyp := 238, conc := 2618, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 239, conc := 2823, proof := sorry })
                      (RArray.leaf { hyp := 240, conc := 1973, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 240, conc := 2621, proof := sorry })
                      (RArray.leaf { hyp := 240, conc := 2824, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 245, conc := 2835, proof := sorry })
                      (RArray.leaf { hyp := 249, conc := 2434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 249, conc := 2637, proof := sorry })
                      (RArray.leaf { hyp := 249, conc := 2840, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 256, conc := 2654, proof := sorry })
                      (RArray.leaf { hyp := 258, conc := 2048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 24, conc := 213, proof := sorry })
                      (RArray.leaf { hyp := 259, conc := 2881, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 261, conc := 2058, proof := sorry })
                      (RArray.leaf { hyp := 264, conc := 2068, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 265, conc := 2690, proof := sorry })
                      (RArray.leaf { hyp := 266, conc := 2691, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 267, conc := 2896, proof := sorry })
                      (RArray.leaf { hyp := 268, conc := 2085, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 25, conc := 1872, proof := sorry })
                      (RArray.leaf { hyp := 25, conc := 4134, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 269, conc := 3175, proof := sorry })
                      (RArray.leaf { hyp := 271, conc := 3178, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 274, conc := 2105, proof := sorry })
                      (RArray.leaf { hyp := 275, conc := 3187, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 276, conc := 2728, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 277, conc := 3190, proof := sorry })
                      (RArray.leaf { hyp := 278, conc := 2122, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 278, conc := 2731, proof := sorry })
                      (RArray.leaf { hyp := 26, conc := 164, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 26, conc := 216, proof := sorry })
                      (RArray.leaf { hyp := 26, conc := 4135, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 281, conc := 2132, proof := sorry })
                      (RArray.leaf { hyp := 285, conc := 2764, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 27, conc := 289, proof := sorry })
                      (RArray.leaf { hyp := 289, conc := 3226, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 290, conc := 3024, proof := sorry })
                      (RArray.leaf { hyp := 291, conc := 3229, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 292, conc := 2176, proof := sorry })
                      (RArray.leaf { hyp := 292, conc := 3027, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 292, conc := 3230, proof := sorry })
                      (RArray.leaf { hyp := 293, conc := 3028, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 297, conc := 3241, proof := sorry })
                      (RArray.leaf { hyp := 28, conc := 2166, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 28, conc := 3993, proof := sorry })
                      (RArray.leaf { hyp := 1, conc := 1998, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 301, conc := 3043, proof := sorry })
                      (RArray.leaf { hyp := 301, conc := 3246, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 307, conc := 3256, proof := sorry })
                      (RArray.leaf { hyp := 308, conc := 3466, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 29, conc := 174, proof := sorry })
                      (RArray.leaf { hyp := 310, conc := 3266, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 310, conc := 3469, proof := sorry })
                      (RArray.leaf { hyp := 311, conc := 3693, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 313, conc := 3696, proof := sorry })
                      (RArray.leaf { hyp := 316, conc := 3286, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 317, conc := 3502, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 317, conc := 3705, proof := sorry })
                      (RArray.leaf { hyp := 318, conc := 3503, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 30, conc := 2794, proof := sorry })
                      (RArray.leaf { hyp := 30, conc := 3819, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 319, conc := 3708, proof := sorry })
                      (RArray.leaf { hyp := 326, conc := 3323, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 327, conc := 3539, proof := sorry })
                      (RArray.leaf { hyp := 328, conc := 3540, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3335, conc := 3304, proof := sorry })
                      (RArray.leaf { hyp := 333, conc := 3350, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 336, conc := 3360, proof := sorry })
                      (RArray.leaf { hyp := 338, conc := 3577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 340, conc := 3377, proof := sorry })
                      (RArray.leaf { hyp := 342, conc := 3836, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 344, conc := 3394, proof := sorry })
                      (RArray.leaf { hyp := 346, conc := 3841, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 33, conc := 249, proof := sorry })
                      (RArray.leaf { hyp := 33, conc := 301, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 357, conc := 3454, proof := sorry })
                      (RArray.leaf { hyp := 359, conc := 3662, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 360, conc := 3872, proof := sorry })
                      (RArray.leaf { hyp := 362, conc := 3672, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 362, conc := 3875, proof := sorry })
                      (RArray.leaf { hyp := 363, conc := 4099, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 365, conc := 3682, proof := sorry })
                      (RArray.leaf { hyp := 365, conc := 4102, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 368, conc := 3692, proof := sorry })
                      (RArray.leaf { hyp := 369, conc := 3908, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 369, conc := 4111, proof := sorry })
                      (RArray.leaf { hyp := 370, conc := 3909, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 371, conc := 4114, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 378, conc := 3729, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3945, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 380, conc := 3946, proof := sorry })
                      (RArray.leaf { hyp := 385, conc := 3756, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 389, conc := 3982, proof := sorry })
                      (RArray.leaf { hyp := 392, conc := 3783, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 393, conc := 4241, proof := sorry })
                      (RArray.leaf { hyp := 394, conc := 4242, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 396, conc := 4560, proof := sorry })
                      (RArray.leaf { hyp := 38, conc := 369, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 400, conc := 3817, proof := sorry })
                      (RArray.leaf { hyp := 400, conc := 4250, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 404, conc := 3834, proof := sorry })
                      (RArray.leaf { hyp := 405, conc := 4058, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 407, conc := 4060, proof := sorry })
                      (RArray.leaf { hyp := 408, conc := 4265, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 39, conc := 3699, proof := sorry })
                      (RArray.leaf { hyp := 41, conc := 3331, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 41, conc := 3543, proof := sorry })
                      (RArray.leaf { hyp := 4307, conc := 4292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4335, conc := 4320, proof := sorry })
                      (RArray.leaf { hyp := 4354, conc := 4342, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 42, conc := 4530, proof := sorry })
                      (RArray.leaf { hyp := 44, conc := 4203, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4622, conc := 4607, proof := sorry })
                      (RArray.leaf { hyp := 4627, conc := 4617, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4650, conc := 4635, proof := sorry })
                      (RArray.leaf { hyp := 4652, conc := 4642, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4669, conc := 4657, proof := sorry })
                      (RArray.leaf { hyp := 4675, conc := 4672, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4692, conc := 4676, proof := sorry })
                      (RArray.leaf { hyp := 4693, conc := 4678, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 357, proof := sorry })
                      (RArray.leaf { hyp := 45, conc := 409, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 47, conc := 414, proof := sorry })
                      (RArray.leaf { hyp := 48, conc := 624, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 11, proof := sorry })
                      (RArray.leaf { hyp := 50, conc := 424, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 50, conc := 627, proof := sorry })
                      (RArray.leaf { hyp := 51, conc := 851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 53, conc := 434, proof := sorry })
                      (RArray.leaf { hyp := 56, conc := 444, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 57, conc := 863, proof := sorry })
                      (RArray.leaf { hyp := 58, conc := 661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 33, proof := sorry })
                      (RArray.leaf { hyp := 59, conc := 866, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 60, conc := 664, proof := sorry })
                      (RArray.leaf { hyp := 60, conc := 867, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 63, conc := 1554, proof := sorry })
                      (RArray.leaf { hyp := 66, conc := 481, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 68, conc := 698, proof := sorry })
                      (RArray.leaf { hyp := 69, conc := 1566, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 70, conc := 1567, proof := sorry })
                      (RArray.leaf { hyp := 70, conc := 498, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 70, conc := 701, proof := sorry })
                      (RArray.leaf { hyp := 73, conc := 508, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 77, conc := 734, proof := sorry })
                      (RArray.leaf { hyp := 6, conc := 1200, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 6, conc := 122, proof := sorry })
                      (RArray.leaf { hyp := 6, conc := 612, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 81, conc := 993, proof := sorry })
                      (RArray.leaf { hyp := 82, conc := 994, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 83, conc := 1605, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 84, conc := 552, proof := sorry })
                      (RArray.leaf { hyp := 84, conc := 997, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 85, conc := 998, proof := sorry })
                      (RArray.leaf { hyp := 89, conc := 1617, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 93, conc := 1013, proof := sorry })
                      (RArray.leaf { hyp := 93, conc := 1622, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 93, conc := 810, proof := sorry })
                      (RArray.leaf { hyp := 97, conc := 591, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 97, conc := 975, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 50, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4031, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 1019, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1020, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 1021, conc := 98, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1023, conc := 423, proof := sorry })
                      (RArray.leaf { hyp := 1024, conc := 7, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1025, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 1026, conc := 627, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 101, conc := 1028, proof := sorry })
                      (RArray.leaf { hyp := 101, conc := 1225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 101, conc := 1631, proof := sorry })
                      (RArray.leaf { hyp := 101, conc := 2448, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 101, conc := 2, proof := sorry })
                      (RArray.leaf { hyp := 101, conc := 3458, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 101, conc := 616, proof := sorry })
                      (RArray.leaf { hyp := 101, conc := 825, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1029, conc := 830, proof := sorry })
                      (RArray.leaf { hyp := 1030, conc := 100, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1031, conc := 101, proof := sorry })
                      (RArray.leaf { hyp := 1031, conc := 414, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1032, conc := 826, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1032, conc := 8, proof := sorry })
                      (RArray.leaf { hyp := 1036, conc := 1236, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1036, conc := 1635, proof := sorry })
                      (RArray.leaf { hyp := 1036, conc := 2461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1036, conc := 3462, proof := sorry })
                      (RArray.leaf { hyp := 1036, conc := 3722, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1036, conc := 427, proof := sorry })
                      (RArray.leaf { hyp := 1036, conc := 840, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1039, conc := 3, proof := sorry })
                      (RArray.leaf { hyp := 1040, conc := 103, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1041, conc := 104, proof := sorry })
                      (RArray.leaf { hyp := 1041, conc := 843, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1042, conc := 1052, proof := sorry })
                      (RArray.leaf { hyp := 1042, conc := 432, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1042, conc := 433, proof := sorry })
                      (RArray.leaf { hyp := 1042, conc := 441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1042, conc := 837, proof := sorry })
                      (RArray.leaf { hyp := 1046, conc := 649, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1049, conc := 55, proof := sorry })
                      (RArray.leaf { hyp := 1050, conc := 106, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1051, conc := 107, proof := sorry })
                      (RArray.leaf { hyp := 1051, conc := 845, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1052, conc := 10, proof := sorry })
                      (RArray.leaf { hyp := 1055, conc := 443, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1055, conc := 847, proof := sorry })
                      (RArray.leaf { hyp := 1056, conc := 3, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1058, conc := 9, proof := sorry })
                      (RArray.leaf { hyp := 1059, conc := 1256, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1060, conc := 451, proof := sorry })
                      (RArray.leaf { hyp := 1063, conc := 10, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1064, conc := 3, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 110, proof := sorry })
                      (RArray.leaf { hyp := 1067, conc := 1229, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 1242, proof := sorry })
                      (RArray.leaf { hyp := 1067, conc := 1261, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 1262, proof := sorry })
                      (RArray.leaf { hyp := 1067, conc := 1263, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 1264, proof := sorry })
                      (RArray.leaf { hyp := 1071, conc := 18, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1071, conc := 3450, proof := sorry })
                      (RArray.leaf { hyp := 1072, conc := 2572, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1072, conc := 4331, proof := sorry })
                      (RArray.leaf { hyp := 1073, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1076, conc := 2098, proof := sorry })
                      (RArray.leaf { hyp := 1078, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1079, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1081, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1083, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1086, conc := 943, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1087, conc := 1140, proof := sorry })
                      (RArray.leaf { hyp := 1087, conc := 2206, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1088, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1089, conc := 1116, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1089, conc := 2778, proof := sorry })
                      (RArray.leaf { hyp := 1089, conc := 4209, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1092, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1093, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1095, conc := 1201, proof := sorry })
                      (RArray.leaf { hyp := 1096, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1097, conc := 1912, proof := sorry })
                      (RArray.leaf { hyp := 1100, conc := 1864, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1100, conc := 2696, proof := sorry })
                      (RArray.leaf { hyp := 1100, conc := 2709, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1100, conc := 2724, proof := sorry })
                      (RArray.leaf { hyp := 1100, conc := 4324, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1101, conc := 483, proof := sorry })
                      (RArray.leaf { hyp := 1110, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1113, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1114, conc := 1771, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1115, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1118, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1118, conc := 150, proof := sorry })
                      (RArray.leaf { hyp := 1118, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1118, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 1118, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1118, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 1118, conc := 98, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1119, conc := 713, proof := sorry })
                      (RArray.leaf { hyp := 1120, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1121, conc := 1933, proof := sorry })
                      (RArray.leaf { hyp := 1124, conc := 2194, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1128, conc := 2177, proof := sorry })
                      (RArray.leaf { hyp := 1129, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1130, conc := 555, proof := sorry })
                      (RArray.leaf { hyp := 1132, conc := 1779, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1132, conc := 1978, proof := sorry })
                      (RArray.leaf { hyp := 1132, conc := 3934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1136, conc := 1995, proof := sorry })
                      (RArray.leaf { hyp := 1140, conc := 168, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1146, conc := 2973, proof := sorry })
                      (RArray.leaf { hyp := 1147, conc := 1366, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 113, conc := 1940, proof := sorry })
                      (RArray.leaf { hyp := 1149, conc := 1762, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1150, conc := 688, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1151, conc := 2575, proof := sorry })
                      (RArray.leaf { hyp := 1155, conc := 2109, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 114, conc := 2733, proof := sorry })
                      (RArray.leaf { hyp := 1162, conc := 1377, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1163, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1164, conc := 724, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1166, conc := 1999, proof := sorry })
                      (RArray.leaf { hyp := 1166, conc := 3988, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1170, conc := 1982, proof := sorry })
                      (RArray.leaf { hyp := 1170, conc := 4145, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 116, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 116, conc := 2099, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1180, conc := 2348, proof := sorry })
                      (RArray.leaf { hyp := 1181, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1183, conc := 1948, proof := sorry })
                      (RArray.leaf { hyp := 117, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 117, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 117, conc := 4379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 117, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 1201, conc := 1911, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1222, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 1223, conc := 98, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1224, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1225, conc := 7, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1226, conc := 99, proof := sorry })
                      (RArray.leaf { hyp := 1227, conc := 98, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1229, conc := 99, proof := sorry })
                      (RArray.leaf { hyp := 1229, conc := 100, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1230, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 1231, conc := 2, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1232, conc := 101, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1232, conc := 1023, proof := sorry })
                      (RArray.leaf { hyp := 1233, conc := 100, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1234, conc := 101, proof := sorry })
                      (RArray.leaf { hyp := 1234, conc := 823, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1235, conc := 101, proof := sorry })
                      (RArray.leaf { hyp := 1235, conc := 1023, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1236, conc := 1033, proof := sorry })
                      (RArray.leaf { hyp := 1239, conc := 103, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1242, conc := 104, proof := sorry })
                      (RArray.leaf { hyp := 1242, conc := 1250, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1243, conc := 1257, proof := sorry })
                      (RArray.leaf { hyp := 1244, conc := 104, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1244, conc := 1248, proof := sorry })
                      (RArray.leaf { hyp := 1245, conc := 105, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1245, conc := 1246, proof := sorry })
                      (RArray.leaf { hyp := 1246, conc := 3726, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 123, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 123, conc := 150, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 123, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 123, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 123, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 123, conc := 7, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1249, conc := 106, proof := sorry })
                      (RArray.leaf { hyp := 1252, conc := 107, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1253, conc := 106, proof := sorry })
                      (RArray.leaf { hyp := 1254, conc := 1252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1255, conc := 10, proof := sorry })
                      (RArray.leaf { hyp := 1256, conc := 850, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1257, conc := 103, proof := sorry })
                      (RArray.leaf { hyp := 1258, conc := 104, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 124, conc := 228, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 124, conc := 4434, proof := sorry })
                      (RArray.leaf { hyp := 124, conc := 72, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1259, conc := 9, proof := sorry })
                      (RArray.leaf { hyp := 1259, conc := 838, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1260, conc := 1245, proof := sorry })
                      (RArray.leaf { hyp := 1260, conc := 833, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1260, conc := 836, proof := sorry })
                      (RArray.leaf { hyp := 1260, conc := 839, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1261, conc := 106, proof := sorry })
                      (RArray.leaf { hyp := 1262, conc := 1252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1263, conc := 1255, proof := sorry })
                      (RArray.leaf { hyp := 1264, conc := 1067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1265, conc := 9, proof := sorry })
                      (RArray.leaf { hyp := 1266, conc := 1255, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1267, conc := 3, proof := sorry })
                      (RArray.leaf { hyp := 1270, conc := 1264, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1274, conc := 18, proof := sorry })
                      (RArray.leaf { hyp := 1276, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 126, conc := 178, proof := sorry })
                      (RArray.leaf { hyp := 1279, conc := 2770, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1281, conc := 520, proof := sorry })
                      (RArray.leaf { hyp := 1282, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1286, conc := 467, proof := sorry })
                      (RArray.leaf { hyp := 1288, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1288, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 1288, conc := 2440, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1288, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 1288, conc := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1288, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 1288, conc := 4379, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1288, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 1289, conc := 960, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1290, conc := 1216, proof := sorry })
                      (RArray.leaf { hyp := 1290, conc := 1317, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1291, conc := 1682, proof := sorry })
                      (RArray.leaf { hyp := 1292, conc := 683, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1293, conc := 2499, proof := sorry })
                      (RArray.leaf { hyp := 1295, conc := 2900, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1296, conc := 698, proof := sorry })
                      (RArray.leaf { hyp := 1298, conc := 1335, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1299, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1300, conc := 2510, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1303, conc := 2916, proof := sorry })
                      (RArray.leaf { hyp := 1304, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 129, conc := 1758, proof := sorry })
                      (RArray.leaf { hyp := 1311, conc := 1628, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1311, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 1311, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1311, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 1312, conc := 46, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1313, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1315, conc := 2330, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1316, conc := 677, proof := sorry })
                      (RArray.leaf { hyp := 1317, conc := 113, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1318, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1319, conc := 710, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1322, conc := 1525, proof := sorry })
                      (RArray.leaf { hyp := 1323, conc := 885, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1324, conc := 2136, proof := sorry })
                      (RArray.leaf { hyp := 1327, conc := 2172, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1331, conc := 2106, proof := sorry })
                      (RArray.leaf { hyp := 1332, conc := 1, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1333, conc := 1367, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1333, conc := 2307, proof := sorry })
                      (RArray.leaf { hyp := 1333, conc := 2788, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1335, conc := 1404, proof := sorry })
                      (RArray.leaf { hyp := 1339, conc := 1170, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1339, conc := 1779, proof := sorry })
                      (RArray.leaf { hyp := 1339, conc := 2198, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1349, conc := 3108, proof := sorry })
                      (RArray.leaf { hyp := 1350, conc := 471, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1352, conc := 158, proof := sorry })
                      (RArray.leaf { hyp := 1353, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1354, conc := 2369, proof := sorry })
                      (RArray.leaf { hyp := 1357, conc := 1976, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1358, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1365, conc := 2177, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1366, conc := 677, proof := sorry })
                      (RArray.leaf { hyp := 1367, conc := 1586, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1369, conc := 2202, proof := sorry })
                      (RArray.leaf { hyp := 1373, conc := 1339, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1373, conc := 2185, proof := sorry })
                      (RArray.leaf { hyp := 1373, conc := 4199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1373, conc := 4676, proof := sorry })
                      (RArray.leaf { hyp := 1383, conc := 2754, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1384, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1386, conc := 2151, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 137, conc := 2226, proof := sorry })
                      (RArray.leaf { hyp := 1404, conc := 137, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1404, conc := 4039, proof := sorry })
                      (RArray.leaf { hyp := 1425, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1429, conc := 151, proof := sorry })
                      (RArray.leaf { hyp := 1429, conc := 3456, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1431, conc := 22, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1432, conc := 2260, proof := sorry })
                      (RArray.leaf { hyp := 1435, conc := 2477, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1437, conc := 1435, proof := sorry })
                      (RArray.leaf { hyp := 1438, conc := 2477, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1439, conc := 1855, proof := sorry })
                      (RArray.leaf { hyp := 1441, conc := 3510, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1443, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 1445, conc := 1441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1445, conc := 1837, proof := sorry })
                      (RArray.leaf { hyp := 1445, conc := 1867, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1446, conc := 4066, proof := sorry })
                      (RArray.leaf { hyp := 1447, conc := 1868, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1448, conc := 157, proof := sorry })
                      (RArray.leaf { hyp := 1451, conc := 208, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1454, conc := 2266, proof := sorry })
                      (RArray.leaf { hyp := 1455, conc := 2269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1457, conc := 160, proof := sorry })
                      (RArray.leaf { hyp := 1457, conc := 214, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1458, conc := 2281, proof := sorry })
                      (RArray.leaf { hyp := 1459, conc := 3526, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1460, conc := 1446, proof := sorry })
                      (RArray.leaf { hyp := 1460, conc := 4133, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1460, conc := 4315, proof := sorry })
                      (RArray.leaf { hyp := 1461, conc := 26, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1462, conc := 26, proof := sorry })
                      (RArray.leaf { hyp := 1464, conc := 1472, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1464, conc := 4359, proof := sorry })
                      (RArray.leaf { hyp := 1465, conc := 1467, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1466, conc := 1469, proof := sorry })
                      (RArray.leaf { hyp := 1466, conc := 2278, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1466, conc := 3330, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1466, conc := 4357, proof := sorry })
                      (RArray.leaf { hyp := 1467, conc := 1841, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1468, conc := 4133, proof := sorry })
                      (RArray.leaf { hyp := 1469, conc := 1669, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1469, conc := 1872, proof := sorry })
                      (RArray.leaf { hyp := 1469, conc := 2270, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1469, conc := 3533, proof := sorry })
                      (RArray.leaf { hyp := 1470, conc := 26, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1480, conc := 3954, proof := sorry })
                      (RArray.leaf { hyp := 1482, conc := 2162, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1483, conc := 3992, proof := sorry })
                      (RArray.leaf { hyp := 1484, conc := 2161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1486, conc := 2163, proof := sorry })
                      (RArray.leaf { hyp := 1488, conc := 254, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1489, conc := 873, proof := sorry })
                      (RArray.leaf { hyp := 1490, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1490, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 1490, conc := 46, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1490, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 1490, conc := 816, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1491, conc := 2134, proof := sorry })
                      (RArray.leaf { hyp := 1492, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1493, conc := 760, proof := sorry })
                      (RArray.leaf { hyp := 1494, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1495, conc := 2145, proof := sorry })
                      (RArray.leaf { hyp := 1495, conc := 3160, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1495, conc := 480, proof := sorry })
                      (RArray.leaf { hyp := 1497, conc := 685, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1498, conc := 3180, proof := sorry })
                      (RArray.leaf { hyp := 1499, conc := 497, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1501, conc := 89, proof := sorry })
                      (RArray.leaf { hyp := 1502, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1503, conc := 2179, proof := sorry })
                      (RArray.leaf { hyp := 1505, conc := 3866, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1505, conc := 722, proof := sorry })
                      (RArray.leaf { hyp := 1506, conc := 1319, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1506, conc := 2169, proof := sorry })
                      (RArray.leaf { hyp := 1506, conc := 2943, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1506, conc := 2957, proof := sorry })
                      (RArray.leaf { hyp := 1507, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1513, conc := 1122, proof := sorry })
                      (RArray.leaf { hyp := 1513, conc := 1625, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1516, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1517, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 150, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 1519, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1520, conc := 1563, proof := sorry })
                      (RArray.leaf { hyp := 1521, conc := 2919, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1522, conc := 3691, proof := sorry })
                      (RArray.leaf { hyp := 1525, conc := 2643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1526, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1527, conc := 918, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1530, conc := 77, proof := sorry })
                      (RArray.leaf { hyp := 1534, conc := 1607, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1535, conc := 3024, proof := sorry })
                      (RArray.leaf { hyp := 1536, conc := 1060, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1536, conc := 1383, proof := sorry })
                      (RArray.leaf { hyp := 1536, conc := 13, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1536, conc := 1901, proof := sorry })
                      (RArray.leaf { hyp := 1536, conc := 2388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1536, conc := 2997, proof := sorry })
                      (RArray.leaf { hyp := 1536, conc := 3293, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1536, conc := 3902, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1536, conc := 4460, proof := sorry })
                      (RArray.leaf { hyp := 1536, conc := 694, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1538, conc := 896, proof := sorry })
                      (RArray.leaf { hyp := 1542, conc := 980, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1546, conc := 790, proof := sorry })
                      (RArray.leaf { hyp := 153, conc := 2260, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1551, conc := 1520, proof := sorry })
                      (RArray.leaf { hyp := 1552, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1553, conc := 1366, proof := sorry })
                      (RArray.leaf { hyp := 1555, conc := 1493, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1555, conc := 1622, proof := sorry })
                      (RArray.leaf { hyp := 1556, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1557, conc := 13, proof := sorry })
                      (RArray.leaf { hyp := 1559, conc := 652, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1559, conc := 959, proof := sorry })
                      (RArray.leaf { hyp := 1560, conc := 724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1561, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1568, conc := 77, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1569, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1570, conc := 1333, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 2684, proof := sorry })
                      (RArray.leaf { hyp := 1572, conc := 805, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1576, conc := 3942, proof := sorry })
                      (RArray.leaf { hyp := 1576, conc := 4676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1576, conc := 777, proof := sorry })
                      (RArray.leaf { hyp := 1576, conc := 967, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 156, conc := 1881, proof := sorry })
                      (RArray.leaf { hyp := 1580, conc := 984, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1585, conc := 4688, proof := sorry })
                      (RArray.leaf { hyp := 1586, conc := 2804, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1587, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1589, conc := 933, proof := sorry })
                      (RArray.leaf { hyp := 1593, conc := 4688, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1593, conc := 618, proof := sorry })
                      (RArray.leaf { hyp := 1593, conc := 726, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1593, conc := 881, proof := sorry })
                      (RArray.leaf { hyp := 1597, conc := 751, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1603, conc := 1750, proof := sorry })
                      (RArray.leaf { hyp := 1603, conc := 1784, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1603, conc := 1801, proof := sorry })
                      (RArray.leaf { hyp := 1603, conc := 1806, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1603, conc := 1821, proof := sorry })
                      (RArray.leaf { hyp := 1603, conc := 1826, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1605, conc := 1934, proof := sorry })
                      (RArray.leaf { hyp := 1606, conc := 1809, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 159, conc := 211, proof := sorry })
                      (RArray.leaf { hyp := 1612, conc := 950, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1617, conc := 1546, proof := sorry })
                      (RArray.leaf { hyp := 1628, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1629, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 1635, conc := 1632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1635, conc := 1838, proof := sorry })
                      (RArray.leaf { hyp := 1635, conc := 1848, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1635, conc := 2248, proof := sorry })
                      (RArray.leaf { hyp := 1635, conc := 2451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1635, conc := 307, proof := sorry })
                      (RArray.leaf { hyp := 1635, conc := 3459, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1635, conc := 4126, proof := sorry })
                      (RArray.leaf { hyp := 1635, conc := 4285, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1638, conc := 26, proof := sorry })
                      (RArray.leaf { hyp := 1639, conc := 152, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1639, conc := 3257, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1640, conc := 1434, proof := sorry })
                      (RArray.leaf { hyp := 1641, conc := 1858, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1644, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 1645, conc := 1855, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1646, conc := 3305, proof := sorry })
                      (RArray.leaf { hyp := 1648, conc := 26, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1650, conc := 1877, proof := sorry })
                      (RArray.leaf { hyp := 1651, conc := 2463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1655, conc := 1851, proof := sorry })
                      (RArray.leaf { hyp := 1655, conc := 3526, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1657, conc := 2469, proof := sorry })
                      (RArray.leaf { hyp := 1658, conc := 2472, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1659, conc := 1870, proof := sorry })
                      (RArray.leaf { hyp := 1660, conc := 2480, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1661, conc := 2484, proof := sorry })
                      (RArray.leaf { hyp := 1662, conc := 2462, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1664, conc := 26, proof := sorry })
                      (RArray.leaf { hyp := 1665, conc := 2282, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1667, conc := 1874, proof := sorry })
                      (RArray.leaf { hyp := 1668, conc := 2274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1669, conc := 2481, proof := sorry })
                      (RArray.leaf { hyp := 1669, conc := 3333, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1672, conc := 2473, proof := sorry })
                      (RArray.leaf { hyp := 1673, conc := 26, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1675, conc := 1878, proof := sorry })
                      (RArray.leaf { hyp := 1681, conc := 3049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1682, conc := 754, proof := sorry })
                      (RArray.leaf { hyp := 1685, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1686, conc := 1030, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 1034, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1686, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 1893, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1686, conc := 2039, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 2160, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1686, conc := 3315, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1687, conc := 2805, proof := sorry })
                      (RArray.leaf { hyp := 1692, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1694, conc := 1931, proof := sorry })
                      (RArray.leaf { hyp := 1694, conc := 2946, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1695, conc := 978, proof := sorry })
                      (RArray.leaf { hyp := 1696, conc := 1639, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1696, conc := 1866, proof := sorry })
                      (RArray.leaf { hyp := 1696, conc := 2160, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1696, conc := 2164, proof := sorry })
                      (RArray.leaf { hyp := 1696, conc := 2168, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1696, conc := 3886, proof := sorry })
                      (RArray.leaf { hyp := 1696, conc := 4082, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1697, conc := 554, proof := sorry })
                      (RArray.leaf { hyp := 1698, conc := 3210, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 168, conc := 1290, proof := sorry })
                      (RArray.leaf { hyp := 1701, conc := 746, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1702, conc := 2112, proof := sorry })
                      (RArray.leaf { hyp := 1702, conc := 793, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1704, conc := 2052, proof := sorry })
                      (RArray.leaf { hyp := 1704, conc := 2086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1704, conc := 2126, proof := sorry })
                      (RArray.leaf { hyp := 1704, conc := 2168, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1704, conc := 3352, proof := sorry })
                      (RArray.leaf { hyp := 1705, conc := 889, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1706, conc := 4646, proof := sorry })
                      (RArray.leaf { hyp := 1706, conc := 691, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1708, conc := 2155, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 169, conc := 176, proof := sorry })
                      (RArray.leaf { hyp := 169, conc := 46, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 169, conc := 65, proof := sorry })
                      (RArray.leaf { hyp := 1709, conc := 1745, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1709, conc := 1864, proof := sorry })
                      (RArray.leaf { hyp := 1709, conc := 2145, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1709, conc := 4496, proof := sorry })
                      (RArray.leaf { hyp := 1709, conc := 694, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1710, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1711, conc := 919, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1713, conc := 1289, proof := sorry })
                      (RArray.leaf { hyp := 1713, conc := 1291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1713, conc := 2108, proof := sorry })
                      (RArray.leaf { hyp := 1713, conc := 2905, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1714, conc := 919, proof := sorry })
                      (RArray.leaf { hyp := 1717, conc := 1745, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1717, conc := 4621, proof := sorry })
                      (RArray.leaf { hyp := 170, conc := 115, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 170, conc := 84, proof := sorry })
                      (RArray.leaf { hyp := 1719, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1722, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1723, conc := 3287, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1723, conc := 4610, proof := sorry })
                      (RArray.leaf { hyp := 1724, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1725, conc := 3146, proof := sorry })
                      (RArray.leaf { hyp := 1728, conc := 2540, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1729, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1733, conc := 1174, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1737, conc := 106, proof := sorry })
                      (RArray.leaf { hyp := 1737, conc := 1257, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1737, conc := 4618, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1738, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1739, conc := 977, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1741, conc := 1815, proof := sorry })
                      (RArray.leaf { hyp := 1749, conc := 1805, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1754, conc := 1899, proof := sorry })
                      (RArray.leaf { hyp := 1755, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1756, conc := 187, proof := sorry })
                      (RArray.leaf { hyp := 1756, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1757, conc := 188, proof := sorry })
                      (RArray.leaf { hyp := 1758, conc := 1926, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1759, conc := 3026, proof := sorry })
                      (RArray.leaf { hyp := 1760, conc := 1909, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1762, conc := 1201, proof := sorry })
                      (RArray.leaf { hyp := 1763, conc := 3090, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1763, conc := 3184, proof := sorry })
                      (RArray.leaf { hyp := 1764, conc := 2990, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 175, conc := 2177, proof := sorry })
                      (RArray.leaf { hyp := 1771, conc := 1749, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1772, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1773, conc := 1116, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1773, conc := 2551, proof := sorry })
                      (RArray.leaf { hyp := 1773, conc := 3809, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1775, conc := 18, proof := sorry })
                      (RArray.leaf { hyp := 176, conc := 169, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1779, conc := 15, proof := sorry })
                      (RArray.leaf { hyp := 1788, conc := 1331, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1789, conc := 25, proof := sorry })
                      (RArray.leaf { hyp := 1789, conc := 3606, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1789, conc := 948, proof := sorry })
                      (RArray.leaf { hyp := 1790, conc := 1587, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1796, conc := 1815, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 178, conc := 126, proof := sorry })
                      (RArray.leaf { hyp := 178, conc := 98, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1800, conc := 181, proof := sorry })
                      (RArray.leaf { hyp := 1808, conc := 1605, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1815, conc := 1095, proof := sorry })
                      (RArray.leaf { hyp := 1815, conc := 2023, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1815, conc := 4039, proof := sorry })
                      (RArray.leaf { hyp := 1815, conc := 4688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 181, conc := 2216, proof := sorry })
                      (RArray.leaf { hyp := 1831, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1834, conc := 1864, proof := sorry })
                      (RArray.leaf { hyp := 1834, conc := 4340, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1835, conc := 1432, proof := sorry })
                      (RArray.leaf { hyp := 1841, conc := 1476, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1843, conc := 1668, proof := sorry })
                      (RArray.leaf { hyp := 1844, conc := 210, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1844, conc := 2248, proof := sorry })
                      (RArray.leaf { hyp := 1844, conc := 4287, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 1429, proof := sorry })
                      (RArray.leaf { hyp := 1848, conc := 1430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 1634, proof := sorry })
                      (RArray.leaf { hyp := 1848, conc := 2242, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 2442, proof := sorry })
                      (RArray.leaf { hyp := 1848, conc := 2475, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 308, proof := sorry })
                      (RArray.leaf { hyp := 1848, conc := 4127, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1849, conc := 4130, proof := sorry })
                      (RArray.leaf { hyp := 1851, conc := 2476, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1853, conc := 1877, proof := sorry })
                      (RArray.leaf { hyp := 1854, conc := 4068, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1854, conc := 4317, proof := sorry })
                      (RArray.leaf { hyp := 1858, conc := 1437, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1861, conc := 1873, proof := sorry })
                      (RArray.leaf { hyp := 1863, conc := 26, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1866, conc := 155, proof := sorry })
                      (RArray.leaf { hyp := 1866, conc := 4066, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1867, conc := 1426, proof := sorry })
                      (RArray.leaf { hyp := 1867, conc := 1444, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1867, conc := 1445, proof := sorry })
                      (RArray.leaf { hyp := 1867, conc := 4126, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1868, conc := 1429, proof := sorry })
                      (RArray.leaf { hyp := 1868, conc := 1447, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1868, conc := 1639, proof := sorry })
                      (RArray.leaf { hyp := 1868, conc := 1866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1868, conc := 1867, proof := sorry })
                      (RArray.leaf { hyp := 1868, conc := 3258, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1868, conc := 3458, proof := sorry })
                      (RArray.leaf { hyp := 1869, conc := 1645, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1870, conc := 1630, proof := sorry })
                      (RArray.leaf { hyp := 1870, conc := 1653, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1870, conc := 1656, proof := sorry })
                      (RArray.leaf { hyp := 1870, conc := 1659, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1871, conc := 1873, proof := sorry })
                      (RArray.leaf { hyp := 1872, conc := 25, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1873, conc := 1632, proof := sorry })
                      (RArray.leaf { hyp := 1873, conc := 4356, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1874, conc := 1667, proof := sorry })
                      (RArray.leaf { hyp := 1876, conc := 156, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1877, conc := 215, proof := sorry })
                      (RArray.leaf { hyp := 1878, conc := 161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1878, conc := 3325, proof := sorry })
                      (RArray.leaf { hyp := 1878, conc := 4133, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 186, conc := 481, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1881, conc := 1465, proof := sorry })
                      (RArray.leaf { hyp := 1883, conc := 7, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1884, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 1885, conc := 2107, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1886, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1888, conc := 170, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1889, conc := 2216, proof := sorry })
                      (RArray.leaf { hyp := 1890, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1891, conc := 2094, proof := sorry })
                      (RArray.leaf { hyp := 1895, conc := 775, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1897, conc := 1085, proof := sorry })
                      (RArray.leaf { hyp := 1898, conc := 1888, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1899, conc := 1087, proof := sorry })
                      (RArray.leaf { hyp := 1900, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1901, conc := 1100, proof := sorry })
                      (RArray.leaf { hyp := 1902, conc := 2105, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 1054, proof := sorry })
                      (RArray.leaf { hyp := 1903, conc := 1257, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 1686, proof := sorry })
                      (RArray.leaf { hyp := 1903, conc := 1700, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 1957, proof := sorry })
                      (RArray.leaf { hyp := 1903, conc := 3352, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 363, proof := sorry })
                      (RArray.leaf { hyp := 1903, conc := 3896, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 4641, proof := sorry })
                      (RArray.leaf { hyp := 1904, conc := 470, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1905, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1907, conc := 18, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1908, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1909, conc := 1089, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1909, conc := 3146, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1910, conc := 2113, proof := sorry })
                      (RArray.leaf { hyp := 1911, conc := 1815, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1912, conc := 1097, proof := sorry })
                      (RArray.leaf { hyp := 1912, conc := 15, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1912, conc := 1763, proof := sorry })
                      (RArray.leaf { hyp := 1912, conc := 2775, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1912, conc := 3972, proof := sorry })
                      (RArray.leaf { hyp := 1913, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1919, conc := 2122, proof := sorry })
                      (RArray.leaf { hyp := 1922, conc := 1368, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1925, conc := 172, proof := sorry })
                      (RArray.leaf { hyp := 1926, conc := 1800, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1927, conc := 3008, proof := sorry })
                      (RArray.leaf { hyp := 1928, conc := 3296, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1928, conc := 3894, proof := sorry })
                      (RArray.leaf { hyp := 1928, conc := 4296, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1928, conc := 507, proof := sorry })
                      (RArray.leaf { hyp := 1929, conc := 1892, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1931, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1931, conc := 1694, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1931, conc := 679, proof := sorry })
                      (RArray.leaf { hyp := 1932, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1933, conc := 1121, proof := sorry })
                      (RArray.leaf { hyp := 1936, conc := 18, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1940, conc := 129, proof := sorry })
                      (RArray.leaf { hyp := 1941, conc := 2913, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1942, conc := 710, proof := sorry })
                      (RArray.leaf { hyp := 1944, conc := 2110, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1948, conc := 1183, proof := sorry })
                      (RArray.leaf { hyp := 1958, conc := 1925, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1959, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1961, conc := 1114, proof := sorry })
                      (RArray.leaf { hyp := 1962, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1963, conc := 1773, proof := sorry })
                      (RArray.leaf { hyp := 1965, conc := 18, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1966, conc := 2585, proof := sorry })
                      (RArray.leaf { hyp := 1966, conc := 561, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1967, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 1968, conc := 2171, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1971, conc := 2174, proof := sorry })
                      (RArray.leaf { hyp := 1972, conc := 1979, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1972, conc := 1984, proof := sorry })
                      (RArray.leaf { hyp := 1972, conc := 1989, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1974, conc := 2133, proof := sorry })
                      (RArray.leaf { hyp := 1975, conc := 2982, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1976, conc := 1706, proof := sorry })
                      (RArray.leaf { hyp := 1976, conc := 2978, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1977, conc := 1994, proof := sorry })
                      (RArray.leaf { hyp := 1977, conc := 83, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1978, conc := 1132, proof := sorry })
                      (RArray.leaf { hyp := 1982, conc := 1037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1982, conc := 1081, proof := sorry })
                      (RArray.leaf { hyp := 1982, conc := 1170, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1991, conc := 18, proof := sorry })
                      (RArray.leaf { hyp := 1992, conc := 3007, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1993, conc := 2921, proof := sorry })
                      (RArray.leaf { hyp := 1994, conc := 173, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1994, conc := 69, proof := sorry })
                      (RArray.leaf { hyp := 1995, conc := 1136, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1999, conc := 1034, proof := sorry })
                      (RArray.leaf { hyp := 1999, conc := 1084, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1999, conc := 1166, proof := sorry })
                      (RArray.leaf { hyp := 1999, conc := 15, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2009, conc := 912, proof := sorry })
                      (RArray.leaf { hyp := 2034, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2038, conc := 266, proof := sorry })
                      (RArray.leaf { hyp := 202, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2041, conc := 2892, proof := sorry })
                      (RArray.leaf { hyp := 2044, conc := 4356, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2045, conc := 2055, proof := sorry })
                      (RArray.leaf { hyp := 2045, conc := 3325, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2045, conc := 4630, proof := sorry })
                      (RArray.leaf { hyp := 2046, conc := 267, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2047, conc := 2667, proof := sorry })
                      (RArray.leaf { hyp := 203, conc := 1845, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2050, conc := 3510, proof := sorry })
                      (RArray.leaf { hyp := 2051, conc := 3512, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2052, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 2053, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2054, conc := 2655, proof := sorry })
                      (RArray.leaf { hyp := 2054, conc := 307, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2055, conc := 3257, proof := sorry })
                      (RArray.leaf { hyp := 2056, conc := 2681, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2057, conc := 2694, proof := sorry })
                      (RArray.leaf { hyp := 2058, conc := 2656, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2060, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2060, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2060, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2060, conc := 306, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2060, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 2061, conc := 257, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2061, conc := 2859, proof := sorry })
                      (RArray.leaf { hyp := 2061, conc := 4597, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2063, conc := 2875, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2064, conc := 2675, proof := sorry })
                      (RArray.leaf { hyp := 2064, conc := 4356, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2065, conc := 3325, proof := sorry })
                      (RArray.leaf { hyp := 2066, conc := 2688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2067, conc := 2879, proof := sorry })
                      (RArray.leaf { hyp := 2068, conc := 2689, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 205, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 205, conc := 150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 205, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 205, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 205, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 205, conc := 306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2070, conc := 2897, proof := sorry })
                      (RArray.leaf { hyp := 2071, conc := 2066, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2073, conc := 2081, proof := sorry })
                      (RArray.leaf { hyp := 2074, conc := 2071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 2687, proof := sorry })
                      (RArray.leaf { hyp := 2075, conc := 2887, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 2890, proof := sorry })
                      (RArray.leaf { hyp := 2075, conc := 3322, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 2075, conc := 3525, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 3536, proof := sorry })
                      (RArray.leaf { hyp := 2075, conc := 4357, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 4672, proof := sorry })
                      (RArray.leaf { hyp := 2078, conc := 2890, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2079, conc := 2038, proof := sorry })
                      (RArray.leaf { hyp := 2081, conc := 4674, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2089, conc := 3954, proof := sorry })
                      (RArray.leaf { hyp := 2091, conc := 3140, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2093, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2094, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2096, conc := 7, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2097, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 2098, conc := 672, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 208, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 208, conc := 1451, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2099, conc := 116, proof := sorry })
                      (RArray.leaf { hyp := 2100, conc := 816, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2101, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2102, conc := 18, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2103, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2104, conc := 1263, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2104, conc := 2591, proof := sorry })
                      (RArray.leaf { hyp := 2104, conc := 2754, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2104, conc := 3496, proof := sorry })
                      (RArray.leaf { hyp := 2104, conc := 4105, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2104, conc := 654, proof := sorry })
                      (RArray.leaf { hyp := 2105, conc := 1929, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2106, conc := 1944, proof := sorry })
                      (RArray.leaf { hyp := 2107, conc := 2910, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2108, conc := 2716, proof := sorry })
                      (RArray.leaf { hyp := 2109, conc := 3126, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2110, conc := 1754, proof := sorry })
                      (RArray.leaf { hyp := 2111, conc := 994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2112, conc := 1333, proof := sorry })
                      (RArray.leaf { hyp := 2112, conc := 1576, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2112, conc := 2943, proof := sorry })
                      (RArray.leaf { hyp := 2115, conc := 897, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2116, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2119, conc := 1916, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2128, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 211, conc := 159, proof := sorry })
                      (RArray.leaf { hyp := 2129, conc := 2143, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2130, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2131, conc := 3691, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2134, conc := 1491, proof := sorry })
                      (RArray.leaf { hyp := 2134, conc := 1518, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2134, conc := 2127, proof := sorry })
                      (RArray.leaf { hyp := 2134, conc := 3149, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2134, conc := 476, proof := sorry })
                      (RArray.leaf { hyp := 2135, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2136, conc := 1324, proof := sorry })
                      (RArray.leaf { hyp := 2139, conc := 168, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2143, conc := 2221, proof := sorry })
                      (RArray.leaf { hyp := 2144, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2145, conc := 1495, proof := sorry })
                      (RArray.leaf { hyp := 2147, conc := 1944, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2151, conc := 1386, proof := sorry })
                      (RArray.leaf { hyp := 214, conc := 1429, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 214, conc := 1456, proof := sorry })
                      (RArray.leaf { hyp := 214, conc := 4356, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2160, conc := 165, proof := sorry })
                      (RArray.leaf { hyp := 2160, conc := 3876, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2161, conc := 1427, proof := sorry })
                      (RArray.leaf { hyp := 2161, conc := 1478, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2161, conc := 1481, proof := sorry })
                      (RArray.leaf { hyp := 2161, conc := 1484, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2162, conc := 1426, proof := sorry })
                      (RArray.leaf { hyp := 2162, conc := 1482, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2163, conc := 167, proof := sorry })
                      (RArray.leaf { hyp := 2164, conc := 1696, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2165, conc := 875, proof := sorry })
                      (RArray.leaf { hyp := 2166, conc := 13, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2168, conc := 1690, proof := sorry })
                      (RArray.leaf { hyp := 2168, conc := 1704, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2168, conc := 2089, proof := sorry })
                      (RArray.leaf { hyp := 2169, conc := 710, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2170, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2176, conc := 1973, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2177, conc := 2211, proof := sorry })
                      (RArray.leaf { hyp := 2178, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2179, conc := 13, proof := sorry })
                      (RArray.leaf { hyp := 2181, conc := 137, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2181, conc := 193, proof := sorry })
                      (RArray.leaf { hyp := 2185, conc := 1373, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2185, conc := 1792, proof := sorry })
                      (RArray.leaf { hyp := 2194, conc := 2147, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2195, conc := 758, proof := sorry })
                      (RArray.leaf { hyp := 2196, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2198, conc := 1339, proof := sorry })
                      (RArray.leaf { hyp := 2198, conc := 3996, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 218, conc := 872, proof := sorry })
                      (RArray.leaf { hyp := 2202, conc := 1369, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2214, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2215, conc := 5, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2221, conc := 1889, proof := sorry })
                      (RArray.leaf { hyp := 2226, conc := 4688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 221, conc := 117, proof := sorry })
                      (RArray.leaf { hyp := 221, conc := 273, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 221, conc := 4434, proof := sorry })
                      (RArray.leaf { hyp := 2237, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2238, conc := 26, proof := sorry })
                      (RArray.leaf { hyp := 2238, conc := 4152, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2240, conc := 1425, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2240, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 2240, conc := 22, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2240, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 2242, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2248, conc := 204, proof := sorry })
                      (RArray.leaf { hyp := 223, conc := 3768, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2249, conc := 2286, proof := sorry })
                      (RArray.leaf { hyp := 2250, conc := 157, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2252, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 2258, conc := 2248, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2259, conc := 158, proof := sorry })
                      (RArray.leaf { hyp := 2260, conc := 1641, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2262, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 2266, conc := 1454, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2268, conc := 24, proof := sorry })
                      (RArray.leaf { hyp := 2269, conc := 1426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2269, conc := 1453, proof := sorry })
                      (RArray.leaf { hyp := 2269, conc := 1455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2270, conc := 1469, proof := sorry })
                      (RArray.leaf { hyp := 2272, conc := 207, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2273, conc := 2277, proof := sorry })
                      (RArray.leaf { hyp := 2274, conc := 1449, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2276, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2277, conc := 1459, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2278, conc := 1466, proof := sorry })
                      (RArray.leaf { hyp := 2278, conc := 1875, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2280, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2281, conc := 1458, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2282, conc := 1641, proof := sorry })
                      (RArray.leaf { hyp := 2285, conc := 1452, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 227, conc := 1044, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 227, conc := 1920, proof := sorry })
                      (RArray.leaf { hyp := 227, conc := 2326, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 227, conc := 2539, proof := sorry })
                      (RArray.leaf { hyp := 227, conc := 2742, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 227, conc := 2935, proof := sorry })
                      (RArray.leaf { hyp := 227, conc := 2, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 227, conc := 3886, proof := sorry })
                      (RArray.leaf { hyp := 2289, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2291, conc := 219, proof := sorry })
                      (RArray.leaf { hyp := 2293, conc := 254, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2294, conc := 2507, proof := sorry })
                      (RArray.leaf { hyp := 2295, conc := 204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2296, conc := 572, proof := sorry })
                      (RArray.leaf { hyp := 2297, conc := 2522, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 228, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 228, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 228, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 228, conc := 98, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2301, conc := 222, proof := sorry })
                      (RArray.leaf { hyp := 2303, conc := 2100, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2304, conc := 2301, proof := sorry })
                      (RArray.leaf { hyp := 2305, conc := 2773, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2306, conc := 704, proof := sorry })
                      (RArray.leaf { hyp := 2307, conc := 2112, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2309, conc := 207, proof := sorry })
                      (RArray.leaf { hyp := 2309, conc := 217, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2310, conc := 723, proof := sorry })
                      (RArray.leaf { hyp := 2311, conc := 2522, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2313, conc := 220, proof := sorry })
                      (RArray.leaf { hyp := 2314, conc := 1, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2315, conc := 2115, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2317, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2318, conc := 886, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2319, conc := 2522, proof := sorry })
                      (RArray.leaf { hyp := 2321, conc := 2332, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2323, conc := 2526, proof := sorry })
                      (RArray.leaf { hyp := 2324, conc := 2527, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2326, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 2328, conc := 29, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2330, conc := 1315, proof := sorry })
                      (RArray.leaf { hyp := 2330, conc := 2939, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2330, conc := 706, proof := sorry })
                      (RArray.leaf { hyp := 2331, conc := 29, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2332, conc := 2375, proof := sorry })
                      (RArray.leaf { hyp := 2333, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2334, conc := 710, proof := sorry })
                      (RArray.leaf { hyp := 2336, conc := 2, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2337, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 2337, conc := 1222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2337, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 2337, conc := 2846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2337, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 2337, conc := 410, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2337, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 2337, conc := 613, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2338, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2342, conc := 4, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2346, conc := 227, proof := sorry })
                      (RArray.leaf { hyp := 2346, conc := 2566, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2347, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2348, conc := 571, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2349, conc := 2552, proof := sorry })
                      (RArray.leaf { hyp := 2350, conc := 2405, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2354, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 2363, conc := 217, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2364, conc := 1076, proof := sorry })
                      (RArray.leaf { hyp := 2365, conc := 2602, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2367, conc := 220, proof := sorry })
                      (RArray.leaf { hyp := 2367, conc := 2302, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2368, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2369, conc := 3127, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2371, conc := 220, proof := sorry })
                      (RArray.leaf { hyp := 2371, conc := 2265, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2372, conc := 1357, proof := sorry })
                      (RArray.leaf { hyp := 2373, conc := 2602, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2375, conc := 2781, proof := sorry })
                      (RArray.leaf { hyp := 2377, conc := 2580, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2378, conc := 2581, proof := sorry })
                      (RArray.leaf { hyp := 2380, conc := 227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2380, conc := 2715, proof := sorry })
                      (RArray.leaf { hyp := 2381, conc := 1155, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2382, conc := 3127, proof := sorry })
                      (RArray.leaf { hyp := 2384, conc := 2405, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2388, conc := 2354, proof := sorry })
                      (RArray.leaf { hyp := 237, conc := 1054, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 237, conc := 3896, proof := sorry })
                      (RArray.leaf { hyp := 2397, conc := 227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2397, conc := 2566, proof := sorry })
                      (RArray.leaf { hyp := 2398, conc := 3130, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2399, conc := 2602, proof := sorry })
                      (RArray.leaf { hyp := 2401, conc := 2354, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2405, conc := 230, proof := sorry })
                      (RArray.leaf { hyp := 2414, conc := 2752, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2416, conc := 2619, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2419, conc := 241, proof := sorry })
                      (RArray.leaf { hyp := 2424, conc := 2622, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 241, conc := 2424, proof := sorry })
                      (RArray.leaf { hyp := 2429, conc := 2835, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2440, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 2441, conc := 26, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2445, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 2446, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2449, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 2449, conc := 150, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2449, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 2449, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2449, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2449, conc := 22, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2449, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 2452, conc := 2286, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2453, conc := 1438, proof := sorry })
                      (RArray.leaf { hyp := 2455, conc := 202, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2461, conc := 204, proof := sorry })
                      (RArray.leaf { hyp := 2462, conc := 1873, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2462, conc := 2488, proof := sorry })
                      (RArray.leaf { hyp := 2463, conc := 1843, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 245, conc := 2280, proof := sorry })
                      (RArray.leaf { hyp := 2469, conc := 1657, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2472, conc := 1629, proof := sorry })
                      (RArray.leaf { hyp := 2472, conc := 1656, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2472, conc := 1658, proof := sorry })
                      (RArray.leaf { hyp := 2472, conc := 1872, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2472, conc := 3522, proof := sorry })
                      (RArray.leaf { hyp := 2473, conc := 1672, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2475, conc := 207, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2476, conc := 1662, proof := sorry })
                      (RArray.leaf { hyp := 2477, conc := 163, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2479, conc := 24, proof := sorry })
                      (RArray.leaf { hyp := 2480, conc := 1654, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2480, conc := 1660, proof := sorry })
                      (RArray.leaf { hyp := 2480, conc := 1872, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2480, conc := 3524, proof := sorry })
                      (RArray.leaf { hyp := 2481, conc := 1669, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2483, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2484, conc := 1661, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2485, conc := 2489, proof := sorry })
                      (RArray.leaf { hyp := 2492, conc := 254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2493, conc := 1151, proof := sorry })
                      (RArray.leaf { hyp := 2493, conc := 4646, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2494, conc := 2291, proof := sorry })
                      (RArray.leaf { hyp := 2497, conc := 2304, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2498, conc := 1040, proof := sorry })
                      (RArray.leaf { hyp := 2498, conc := 1903, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2498, conc := 2321, proof := sorry })
                      (RArray.leaf { hyp := 2498, conc := 2414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2498, conc := 3107, proof := sorry })
                      (RArray.leaf { hyp := 2498, conc := 3802, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2498, conc := 3882, proof := sorry })
                      (RArray.leaf { hyp := 23, conc := 26, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2499, conc := 290, proof := sorry })
                      (RArray.leaf { hyp := 2500, conc := 225, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2502, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 2504, conc := 2497, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2506, conc := 2912, proof := sorry })
                      (RArray.leaf { hyp := 2506, conc := 4434, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2507, conc := 2504, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2508, conc := 2922, proof := sorry })
                      (RArray.leaf { hyp := 2509, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2510, conc := 3127, proof := sorry })
                      (RArray.leaf { hyp := 2512, conc := 3209, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2513, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2514, conc := 2500, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2516, conc := 2604, proof := sorry })
                      (RArray.leaf { hyp := 2516, conc := 2686, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2517, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2518, conc := 3210, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2520, conc := 3162, proof := sorry })
                      (RArray.leaf { hyp := 2521, conc := 758, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2522, conc := 2514, proof := sorry })
                      (RArray.leaf { hyp := 2526, conc := 2323, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2531, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2534, conc := 29, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2535, conc := 2557, proof := sorry })
                      (RArray.leaf { hyp := 2535, conc := 2664, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2535, conc := 3092, proof := sorry })
                      (RArray.leaf { hyp := 2535, conc := 3144, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2535, conc := 3179, proof := sorry })
                      (RArray.leaf { hyp := 2536, conc := 2091, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2538, conc := 2335, proof := sorry })
                      (RArray.leaf { hyp := 2541, conc := 29, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2545, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2549, conc := 27, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2549, conc := 2803, proof := sorry })
                      (RArray.leaf { hyp := 2550, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2551, conc := 951, proof := sorry })
                      (RArray.leaf { hyp := 2553, conc := 245, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2557, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 254, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2566, conc := 3023, proof := sorry })
                      (RArray.leaf { hyp := 2566, conc := 3121, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2566, conc := 363, proof := sorry })
                      (RArray.leaf { hyp := 2567, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2568, conc := 239, proof := sorry })
                      (RArray.leaf { hyp := 255, conc := 2679, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2570, conc := 220, proof := sorry })
                      (RArray.leaf { hyp := 2570, conc := 2723, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2571, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2572, conc := 1154, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2574, conc := 2524, proof := sorry })
                      (RArray.leaf { hyp := 2576, conc := 2568, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2578, conc := 2719, proof := sorry })
                      (RArray.leaf { hyp := 256, conc := 2848, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 256, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 2583, conc := 227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2583, conc := 3175, proof := sorry })
                      (RArray.leaf { hyp := 2584, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2585, conc := 1789, proof := sorry })
                      (RArray.leaf { hyp := 2587, conc := 230, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2587, conc := 2745, proof := sorry })
                      (RArray.leaf { hyp := 257, conc := 262, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 257, conc := 2662, proof := sorry })
                      (RArray.leaf { hyp := 257, conc := 2849, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 257, conc := 3458, proof := sorry })
                      (RArray.leaf { hyp := 2591, conc := 3200, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2600, conc := 2820, proof := sorry })
                      (RArray.leaf { hyp := 2601, conc := 1634, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2601, conc := 1728, proof := sorry })
                      (RArray.leaf { hyp := 2601, conc := 1739, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2602, conc := 2576, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2604, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 2608, conc := 282, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2617, conc := 1957, proof := sorry })
                      (RArray.leaf { hyp := 2617, conc := 2363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2617, conc := 237, proof := sorry })
                      (RArray.leaf { hyp := 2619, conc := 2416, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2622, conc := 241, proof := sorry })
                      (RArray.leaf { hyp := 2632, conc := 2578, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 262, conc := 2643, proof := sorry })
                      (RArray.leaf { hyp := 262, conc := 2846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 262, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 2643, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2644, conc := 268, proof := sorry })
                      (RArray.leaf { hyp := 2644, conc := 37, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2648, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2652, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2652, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2652, conc := 2874, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2652, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 2652, conc := 3455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2653, conc := 2863, proof := sorry })
                      (RArray.leaf { hyp := 2654, conc := 256, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2655, conc := 2054, proof := sorry })
                      (RArray.leaf { hyp := 2655, conc := 2885, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2655, conc := 3459, proof := sorry })
                      (RArray.leaf { hyp := 2655, conc := 4356, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2656, conc := 2866, proof := sorry })
                      (RArray.leaf { hyp := 2660, conc := 2691, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2662, conc := 257, proof := sorry })
                      (RArray.leaf { hyp := 2663, conc := 2883, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2665, conc := 2859, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2665, conc := 3459, proof := sorry })
                      (RArray.leaf { hyp := 2666, conc := 2863, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2670, conc := 2660, proof := sorry })
                      (RArray.leaf { hyp := 2670, conc := 2869, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2672, conc := 2063, proof := sorry })
                      (RArray.leaf { hyp := 2673, conc := 2897, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2675, conc := 2886, proof := sorry })
                      (RArray.leaf { hyp := 2676, conc := 2078, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2678, conc := 259, proof := sorry })
                      (RArray.leaf { hyp := 2679, conc := 2847, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2680, conc := 2647, proof := sorry })
                      (RArray.leaf { hyp := 2682, conc := 262, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2683, conc := 2891, proof := sorry })
                      (RArray.leaf { hyp := 2684, conc := 2075, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2686, conc := 2661, proof := sorry })
                      (RArray.leaf { hyp := 2687, conc := 2067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2687, conc := 4340, proof := sorry })
                      (RArray.leaf { hyp := 2688, conc := 2068, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2690, conc := 2857, proof := sorry })
                      (RArray.leaf { hyp := 2691, conc := 2895, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2692, conc := 2677, proof := sorry })
                      (RArray.leaf { hyp := 2695, conc := 202, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2697, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2700, conc := 674, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2701, conc := 2248, proof := sorry })
                      (RArray.leaf { hyp := 2702, conc := 186, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2703, conc := 68, proof := sorry })
                      (RArray.leaf { hyp := 2705, conc := 22, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2706, conc := 114, proof := sorry })
                      (RArray.leaf { hyp := 2706, conc := 4331, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2707, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 269, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 269, conc := 2695, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 269, conc := 2898, proof := sorry })
                      (RArray.leaf { hyp := 269, conc := 4079, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2710, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2711, conc := 2242, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2711, conc := 2262, proof := sorry })
                      (RArray.leaf { hyp := 2711, conc := 2442, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2711, conc := 2475, proof := sorry })
                      (RArray.leaf { hyp := 2711, conc := 3141, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2711, conc := 322, proof := sorry })
                      (RArray.leaf { hyp := 2712, conc := 2787, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2713, conc := 1170, proof := sorry })
                      (RArray.leaf { hyp := 2713, conc := 1760, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2713, conc := 1792, proof := sorry })
                      (RArray.leaf { hyp := 2713, conc := 1995, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2713, conc := 2537, proof := sorry })
                      (RArray.leaf { hyp := 2715, conc := 1024, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2715, conc := 1846, proof := sorry })
                      (RArray.leaf { hyp := 2715, conc := 2252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2715, conc := 2475, proof := sorry })
                      (RArray.leaf { hyp := 2715, conc := 2566, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2715, conc := 3866, proof := sorry })
                      (RArray.leaf { hyp := 2716, conc := 687, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2717, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 270, conc := 1684, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 270, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 2719, conc := 2904, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2720, conc := 1904, proof := sorry })
                      (RArray.leaf { hyp := 2721, conc := 1912, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2723, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2723, conc := 30, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2724, conc := 1901, proof := sorry })
                      (RArray.leaf { hyp := 2724, conc := 30, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2724, conc := 3499, proof := sorry })
                      (RArray.leaf { hyp := 2724, conc := 4097, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2725, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2725, conc := 2838, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2727, conc := 2959, proof := sorry })
                      (RArray.leaf { hyp := 2732, conc := 22, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2734, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2736, conc := 1721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2736, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 2736, conc := 3142, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2737, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2738, conc := 24, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 272, conc := 2458, proof := sorry })
                      (RArray.leaf { hyp := 2739, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2740, conc := 1725, proof := sorry })
                      (RArray.leaf { hyp := 2740, conc := 1864, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2740, conc := 2473, proof := sorry })
                      (RArray.leaf { hyp := 2740, conc := 25, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2740, conc := 3213, proof := sorry })
                      (RArray.leaf { hyp := 2740, conc := 3488, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2740, conc := 4108, proof := sorry })
                      (RArray.leaf { hyp := 2740, conc := 4611, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2744, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2748, conc := 4, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2752, conc := 2600, proof := sorry })
                      (RArray.leaf { hyp := 2753, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2754, conc := 1536, proof := sorry })
                      (RArray.leaf { hyp := 2754, conc := 1739, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2754, conc := 2104, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2754, conc := 2318, proof := sorry })
                      (RArray.leaf { hyp := 2754, conc := 4490, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2756, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2760, conc := 30, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 275, conc := 2106, proof := sorry })
                      (RArray.leaf { hyp := 2769, conc := 217, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2770, conc := 2774, proof := sorry })
                      (RArray.leaf { hyp := 2771, conc := 994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2773, conc := 2284, proof := sorry })
                      (RArray.leaf { hyp := 2773, conc := 2299, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2773, conc := 2302, proof := sorry })
                      (RArray.leaf { hyp := 2773, conc := 2305, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2774, conc := 2381, proof := sorry })
                      (RArray.leaf { hyp := 2775, conc := 3184, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2777, conc := 210, proof := sorry })
                      (RArray.leaf { hyp := 2777, conc := 220, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2778, conc := 1901, proof := sorry })
                      (RArray.leaf { hyp := 2778, conc := 3181, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2779, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2781, conc := 223, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2786, conc := 2566, proof := sorry })
                      (RArray.leaf { hyp := 2786, conc := 2583, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2787, conc := 537, proof := sorry })
                      (RArray.leaf { hyp := 2788, conc := 1266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2788, conc := 1386, proof := sorry })
                      (RArray.leaf { hyp := 2788, conc := 2318, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2788, conc := 2963, proof := sorry })
                      (RArray.leaf { hyp := 2788, conc := 646, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2788, conc := 894, proof := sorry })
                      (RArray.leaf { hyp := 2788, conc := 897, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2788, conc := 951, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 277, conc := 304, proof := sorry })
                      (RArray.leaf { hyp := 2790, conc := 2429, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2794, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 2803, conc := 227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2803, conc := 269, proof := sorry })
                      (RArray.leaf { hyp := 2804, conc := 1367, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2805, conc := 1350, proof := sorry })
                      (RArray.leaf { hyp := 279, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2811, conc := 230, proof := sorry })
                      (RArray.leaf { hyp := 280, conc := 65, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2820, conc := 2617, proof := sorry })
                      (RArray.leaf { hyp := 2835, conc := 2363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2835, conc := 245, proof := sorry })
                      (RArray.leaf { hyp := 2846, conc := 0, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2847, conc := 2689, proof := sorry })
                      (RArray.leaf { hyp := 2849, conc := 2059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2849, conc := 4655, proof := sorry })
                      (RArray.leaf { hyp := 2855, conc := 254, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2857, conc := 2893, proof := sorry })
                      (RArray.leaf { hyp := 2858, conc := 261, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2859, conc := 2061, proof := sorry })
                      (RArray.leaf { hyp := 2859, conc := 260, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2859, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 2859, conc := 2659, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2859, conc := 307, proof := sorry })
                      (RArray.leaf { hyp := 2859, conc := 3456, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2859, conc := 3457, proof := sorry })
                      (RArray.leaf { hyp := 2860, conc := 2880, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2861, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2863, conc := 2860, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2866, conc := 2692, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2867, conc := 256, proof := sorry })
                      (RArray.leaf { hyp := 2868, conc := 2850, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2869, conc := 2895, proof := sorry })
                      (RArray.leaf { hyp := 2875, conc := 2672, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2876, conc := 2057, proof := sorry })
                      (RArray.leaf { hyp := 2878, conc := 2650, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2879, conc := 2687, proof := sorry })
                      (RArray.leaf { hyp := 2880, conc := 2884, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2881, conc := 259, proof := sorry })
                      (RArray.leaf { hyp := 2882, conc := 4356, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2883, conc := 2853, proof := sorry })
                      (RArray.leaf { hyp := 2886, conc := 2064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2887, conc := 2684, proof := sorry })
                      (RArray.leaf { hyp := 2889, conc := 262, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2889, conc := 2648, proof := sorry })
                      (RArray.leaf { hyp := 2890, conc := 2676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2890, conc := 3330, proof := sorry })
                      (RArray.leaf { hyp := 2891, conc := 2679, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2892, conc := 2670, proof := sorry })
                      (RArray.leaf { hyp := 2893, conc := 265, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2893, conc := 322, proof := sorry })
                      (RArray.leaf { hyp := 2897, conc := 2663, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2898, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 27, conc := 103, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 27, conc := 2705, proof := sorry })
                      (RArray.leaf { hyp := 2900, conc := 1498, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2903, conc := 29, proof := sorry })
                      (RArray.leaf { hyp := 2904, conc := 2727, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2904, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2905, conc := 493, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2906, conc := 1521, proof := sorry })
                      (RArray.leaf { hyp := 2907, conc := 3147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2910, conc := 995, proof := sorry })
                      (RArray.leaf { hyp := 2912, conc := 1288, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2912, conc := 2506, proof := sorry })
                      (RArray.leaf { hyp := 2912, conc := 3115, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2913, conc := 1500, proof := sorry })
                      (RArray.leaf { hyp := 2914, conc := 2632, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2915, conc := 2009, proof := sorry })
                      (RArray.leaf { hyp := 2916, conc := 2518, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2917, conc := 2536, proof := sorry })
                      (RArray.leaf { hyp := 2918, conc := 2881, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 290, conc := 1279, proof := sorry })
                      (RArray.leaf { hyp := 290, conc := 66, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2919, conc := 1150, proof := sorry })
                      (RArray.leaf { hyp := 2919, conc := 2310, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2919, conc := 2728, proof := sorry })
                      (RArray.leaf { hyp := 2920, conc := 889, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2921, conc := 1927, proof := sorry })
                      (RArray.leaf { hyp := 2922, conc := 2627, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2923, conc := 1146, proof := sorry })
                      (RArray.leaf { hyp := 2924, conc := 2521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2926, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2927, conc := 748, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2928, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 291, conc := 1122, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2931, conc := 2306, proof := sorry })
                      (RArray.leaf { hyp := 2932, conc := 3135, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2934, conc := 3137, proof := sorry })
                      (RArray.leaf { hyp := 2935, conc := 22, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2937, conc := 2921, proof := sorry })
                      (RArray.leaf { hyp := 2940, conc := 2975, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2941, conc := 4, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2942, conc := 3122, proof := sorry })
                      (RArray.leaf { hyp := 2943, conc := 724, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2944, conc := 1316, proof := sorry })
                      (RArray.leaf { hyp := 2947, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2951, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2955, conc := 27, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2956, conc := 469, proof := sorry })
                      (RArray.leaf { hyp := 2957, conc := 758, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2959, conc := 2524, proof := sorry })
                      (RArray.leaf { hyp := 2963, conc := 30, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2972, conc := 3175, proof := sorry })
                      (RArray.leaf { hyp := 2973, conc := 1682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2974, conc := 2975, proof := sorry })
                      (RArray.leaf { hyp := 2976, conc := 2508, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2977, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 2978, conc := 745, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2980, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 2981, conc := 748, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2982, conc := 1293, proof := sorry })
                      (RArray.leaf { hyp := 2986, conc := 3189, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2988, conc := 3191, proof := sorry })
                      (RArray.leaf { hyp := 2989, conc := 3006, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2990, conc := 1705, proof := sorry })
                      (RArray.leaf { hyp := 2991, conc := 2372, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2993, conc := 282, proof := sorry })
                      (RArray.leaf { hyp := 2997, conc := 3010, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 28, conc := 4457, proof := sorry })
                      (RArray.leaf { hyp := 3006, conc := 279, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3007, conc := 1709, proof := sorry })
                      (RArray.leaf { hyp := 3008, conc := 474, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3010, conc := 30, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3014, conc := 2719, proof := sorry })
                      (RArray.leaf { hyp := 3026, conc := 3118, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3026, conc := 3134, proof := sorry })
                      (RArray.leaf { hyp := 3049, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3050, conc := 3081, proof := sorry })
                      (RArray.leaf { hyp := 3052, conc := 3082, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3056, conc := 3072, proof := sorry })
                      (RArray.leaf { hyp := 3058, conc := 3077, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3058, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 3060, conc := 3096, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3061, conc := 3100, proof := sorry })
                      (RArray.leaf { hyp := 3062, conc := 3071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3062, conc := 37, proof := sorry })
                      (RArray.leaf { hyp := 3069, conc := 3097, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3070, conc := 322, proof := sorry })
                      (RArray.leaf { hyp := 3071, conc := 3061, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3072, conc := 3083, proof := sorry })
                      (RArray.leaf { hyp := 3076, conc := 3079, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3077, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3080, conc := 3060, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3081, conc := 3083, proof := sorry })
                      (RArray.leaf { hyp := 3082, conc := 3093, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3083, conc := 3073, proof := sorry })
                      (RArray.leaf { hyp := 3085, conc := 3059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3086, conc := 3076, proof := sorry })
                      (RArray.leaf { hyp := 3088, conc := 3070, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3089, conc := 3062, proof := sorry })
                      (RArray.leaf { hyp := 3092, conc := 3070, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3093, conc := 3052, proof := sorry })
                      (RArray.leaf { hyp := 3093, conc := 4655, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3094, conc := 3089, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3101, conc := 2, proof := sorry })
                      (RArray.leaf { hyp := 3102, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3102, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 3103, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3104, conc := 2440, proof := sorry })
                      (RArray.leaf { hyp := 3106, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 1037, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 1224, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 1440, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 1663, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 1686, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 1866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 220, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 227, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2284, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 2292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2299, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 2302, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2329, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 2336, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2495, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 2512, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2654, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 2661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 2735, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 3308, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 332, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 3342, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 3345, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 3508, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 3545, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 3663, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 3711, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 3758, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 3879, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 4283, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 4290, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 4319, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 4381, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 4395, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 4444, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 4641, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3107, conc := 615, proof := sorry })
                      (RArray.leaf { hyp := 3107, conc := 821, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3108, conc := 2923, proof := sorry })
                      (RArray.leaf { hyp := 3109, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3110, conc := 3147, proof := sorry })
                      (RArray.leaf { hyp := 3112, conc := 22, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3113, conc := 889, proof := sorry })
                      (RArray.leaf { hyp := 3116, conc := 1885, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3117, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 3118, conc := 3116, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3119, conc := 758, proof := sorry })
                      (RArray.leaf { hyp := 3120, conc := 3110, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3121, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 3121, conc := 2049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3121, conc := 2658, proof := sorry })
                      (RArray.leaf { hyp := 3121, conc := 2881, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3121, conc := 3175, proof := sorry })
                      (RArray.leaf { hyp := 3121, conc := 4069, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3122, conc := 506, proof := sorry })
                      (RArray.leaf { hyp := 3122, conc := 684, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3123, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3124, conc := 3239, proof := sorry })
                      (RArray.leaf { hyp := 3125, conc := 4, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3126, conc := 1895, proof := sorry })
                      (RArray.leaf { hyp := 3127, conc := 1300, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3127, conc := 555, proof := sorry })
                      (RArray.leaf { hyp := 3127, conc := 561, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3128, conc := 2925, proof := sorry })
                      (RArray.leaf { hyp := 3129, conc := 2632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3130, conc := 758, proof := sorry })
                      (RArray.leaf { hyp := 3131, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3134, conc := 3227, proof := sorry })
                      (RArray.leaf { hyp := 3136, conc := 2933, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3138, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3140, conc := 673, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3141, conc := 22, proof := sorry })
                      (RArray.leaf { hyp := 3143, conc := 1489, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3144, conc := 1671, proof := sorry })
                      (RArray.leaf { hyp := 3144, conc := 1723, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3144, conc := 2553, proof := sorry })
                      (RArray.leaf { hyp := 3144, conc := 2738, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3144, conc := 311, proof := sorry })
                      (RArray.leaf { hyp := 3144, conc := 3196, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3145, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 3146, conc := 2740, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3147, conc := 3120, proof := sorry })
                      (RArray.leaf { hyp := 313, conc := 310, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 313, conc := 316, proof := sorry })
                      (RArray.leaf { hyp := 313, conc := 317, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 313, conc := 318, proof := sorry })
                      (RArray.leaf { hyp := 313, conc := 320, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3150, conc := 907, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3154, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 1034, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 1477, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 165, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 1883, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 217, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 2289, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 2566, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 2, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 363, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3158, conc := 4384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3158, conc := 831, proof := sorry })
                      (RArray.leaf { hyp := 314, conc := 3277, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3159, conc := 2700, proof := sorry })
                      (RArray.leaf { hyp := 3160, conc := 2131, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3161, conc := 292, proof := sorry })
                      (RArray.leaf { hyp := 3162, conc := 2632, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3166, conc := 30, proof := sorry })
                      (RArray.leaf { hyp := 3175, conc := 1237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3175, conc := 269, proof := sorry })
                      (RArray.leaf { hyp := 3176, conc := 1764, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3177, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 3179, conc := 24, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3179, conc := 2711, proof := sorry })
                      (RArray.leaf { hyp := 3180, conc := 672, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3181, conc := 2713, proof := sorry })
                      (RArray.leaf { hyp := 3183, conc := 4, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3184, conc := 2721, proof := sorry })
                      (RArray.leaf { hyp := 3185, conc := 1, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3186, conc := 2983, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3188, conc := 2985, proof := sorry })
                      (RArray.leaf { hyp := 3190, conc := 3244, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3192, conc := 27, proof := sorry })
                      (RArray.leaf { hyp := 3192, conc := 618, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3193, conc := 883, proof := sorry })
                      (RArray.leaf { hyp := 3194, conc := 2179, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3195, conc := 489, proof := sorry })
                      (RArray.leaf { hyp := 3209, conc := 3158, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3210, conc := 758, proof := sorry })
                      (RArray.leaf { hyp := 3211, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3212, conc := 3161, proof := sorry })
                      (RArray.leaf { hyp := 3213, conc := 2557, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3217, conc := 4, proof := sorry })
                      (RArray.leaf { hyp := 3252, conc := 0, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3253, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3259, conc := 3265, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3265, conc := 309, proof := sorry })
                      (RArray.leaf { hyp := 3269, conc := 3298, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3272, conc := 3294, proof := sorry })
                      (RArray.leaf { hyp := 3273, conc := 3287, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3274, conc := 3300, proof := sorry })
                      (RArray.leaf { hyp := 3274, conc := 3302, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3275, conc := 319, proof := sorry })
                      (RArray.leaf { hyp := 3276, conc := 3266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3276, conc := 3294, proof := sorry })
                      (RArray.leaf { hyp := 3276, conc := 3303, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3279, conc := 3256, proof := sorry })
                      (RArray.leaf { hyp := 3279, conc := 3282, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3279, conc := 3283, proof := sorry })
                      (RArray.leaf { hyp := 3279, conc := 3284, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3279, conc := 3286, proof := sorry })
                      (RArray.leaf { hyp := 3281, conc := 3285, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3282, conc := 3302, proof := sorry })
                      (RArray.leaf { hyp := 3283, conc := 3287, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3288, conc := 3300, proof := sorry })
                      (RArray.leaf { hyp := 3289, conc := 3301, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3290, conc := 3303, proof := sorry })
                      (RArray.leaf { hyp := 3292, conc := 319, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3295, conc := 3287, proof := sorry })
                      (RArray.leaf { hyp := 3297, conc := 3302, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3309, conc := 37, proof := sorry })
                      (RArray.leaf { hyp := 3316, conc := 324, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3319, conc := 325, proof := sorry })
                      (RArray.leaf { hyp := 3323, conc := 307, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3323, conc := 326, proof := sorry })
                      (RArray.leaf { hyp := 3323, conc := 3526, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3323, conc := 4356, proof := sorry })
                      (RArray.leaf { hyp := 3328, conc := 37, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 331, conc := 386, proof := sorry })
                      (RArray.leaf { hyp := 331, conc := 4342, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3331, conc := 3340, proof := sorry })
                      (RArray.leaf { hyp := 3343, conc := 3347, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3343, conc := 3805, proof := sorry })
                      (RArray.leaf { hyp := 3343, conc := 4246, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3346, conc := 4194, proof := sorry })
                      (RArray.leaf { hyp := 3347, conc := 3564, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3347, conc := 4177, proof := sorry })
                      (RArray.leaf { hyp := 3348, conc := 3450, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3349, conc := 4228, proof := sorry })
                      (RArray.leaf { hyp := 3350, conc := 3377, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3353, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3354, conc := 4064, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3355, conc := 3299, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3355, conc := 3450, proof := sorry })
                      (RArray.leaf { hyp := 3357, conc := 3560, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 334, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 334, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 334, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3361, conc := 3376, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3362, conc := 3430, proof := sorry })
                      (RArray.leaf { hyp := 3363, conc := 3566, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3364, conc := 3438, proof := sorry })
                      (RArray.leaf { hyp := 3365, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3369, conc := 3330, proof := sorry })
                      (RArray.leaf { hyp := 3369, conc := 3363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3369, conc := 3525, proof := sorry })
                      (RArray.leaf { hyp := 3369, conc := 4025, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3369, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 3369, conc := 42, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3373, conc := 3377, proof := sorry })
                      (RArray.leaf { hyp := 3382, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3383, conc := 3435, proof := sorry })
                      (RArray.leaf { hyp := 3384, conc := 3769, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3384, conc := 4196, proof := sorry })
                      (RArray.leaf { hyp := 3385, conc := 3411, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3387, conc := 4361, proof := sorry })
                      (RArray.leaf { hyp := 337, conc := 397, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3391, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 3396, conc := 4373, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3400, conc := 3374, proof := sorry })
                      (RArray.leaf { hyp := 3401, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3403, conc := 4196, proof := sorry })
                      (RArray.leaf { hyp := 3404, conc := 3450, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3416, conc := 3600, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3416, conc := 4006, proof := sorry })
                      (RArray.leaf { hyp := 3416, conc := 42, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3418, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3435, conc := 3445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3455, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 3472, conc := 3501, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3475, conc := 3497, proof := sorry })
                      (RArray.leaf { hyp := 3476, conc := 3498, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3477, conc := 3503, proof := sorry })
                      (RArray.leaf { hyp := 3478, conc := 3505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3479, conc := 3493, proof := sorry })
                      (RArray.leaf { hyp := 3482, conc := 3459, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3482, conc := 3486, proof := sorry })
                      (RArray.leaf { hyp := 3482, conc := 3487, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3482, conc := 3488, proof := sorry })
                      (RArray.leaf { hyp := 3482, conc := 3489, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3484, conc := 3499, proof := sorry })
                      (RArray.leaf { hyp := 3485, conc := 3472, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3486, conc := 3498, proof := sorry })
                      (RArray.leaf { hyp := 3491, conc := 3503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3492, conc := 3504, proof := sorry })
                      (RArray.leaf { hyp := 3493, conc := 3506, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3494, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 3494, conc := 3277, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3494, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 33, conc := 3823, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3500, conc := 3292, proof := sorry })
                      (RArray.leaf { hyp := 3500, conc := 3465, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3500, conc := 3485, proof := sorry })
                      (RArray.leaf { hyp := 3503, conc := 3708, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3527, conc := 41, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3538, conc := 41, proof := sorry })
                      (RArray.leaf { hyp := 3546, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3549, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3550, conc := 3974, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3551, conc := 354, proof := sorry })
                      (RArray.leaf { hyp := 3552, conc := 3369, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3556, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3560, conc := 3576, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3564, conc := 4211, proof := sorry })
                      (RArray.leaf { hyp := 3565, conc := 332, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3565, conc := 3802, proof := sorry })
                      (RArray.leaf { hyp := 3565, conc := 4455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3566, conc := 3369, proof := sorry })
                      (RArray.leaf { hyp := 3566, conc := 4215, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3567, conc := 3580, proof := sorry })
                      (RArray.leaf { hyp := 3568, conc := 3956, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3572, conc := 3349, proof := sorry })
                      (RArray.leaf { hyp := 3572, conc := 42, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3576, conc := 3343, proof := sorry })
                      (RArray.leaf { hyp := 3582, conc := 342, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3582, conc := 374, proof := sorry })
                      (RArray.leaf { hyp := 3582, conc := 3988, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3582, conc := 4528, proof := sorry })
                      (RArray.leaf { hyp := 3586, conc := 342, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3586, conc := 377, proof := sorry })
                      (RArray.leaf { hyp := 3586, conc := 3992, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3586, conc := 4532, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 3387, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3590, conc := 3616, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 3739, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3590, conc := 3793, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 4022, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3590, conc := 4199, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 4423, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3590, conc := 4524, proof := sorry })
                      (RArray.leaf { hyp := 3590, conc := 4676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3598, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3599, conc := 342, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3599, conc := 384, proof := sorry })
                      (RArray.leaf { hyp := 3599, conc := 4005, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3599, conc := 4545, proof := sorry })
                      (RArray.leaf { hyp := 3600, conc := 4134, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3606, conc := 3525, proof := sorry })
                      (RArray.leaf { hyp := 3606, conc := 4134, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3606, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 3606, conc := 4368, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3606, conc := 4655, proof := sorry })
                      (RArray.leaf { hyp := 3608, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3616, conc := 3819, proof := sorry })
                      (RArray.leaf { hyp := 3619, conc := 3958, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3621, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 361, conc := 4067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3633, conc := 4563, proof := sorry })
                      (RArray.leaf { hyp := 3658, conc := 0, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 365, conc := 362, proof := sorry })
                      (RArray.leaf { hyp := 365, conc := 369, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 365, conc := 370, proof := sorry })
                      (RArray.leaf { hyp := 365, conc := 371, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 365, conc := 372, proof := sorry })
                      (RArray.leaf { hyp := 3670, conc := 3661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3671, conc := 3664, proof := sorry })
                      (RArray.leaf { hyp := 3675, conc := 3704, proof := sorry })))))))))))

end EndToEnd
