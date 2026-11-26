import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
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
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def _root_.EndToEnd.pos2 : RArray EndToEnd.PosFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3163, conc := 3157, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3164, conc := 3163, proof := sorry })
                      (RArray.leaf { hyp := 3167, conc := 3165, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3168, conc := 3167, proof := sorry })
                      (RArray.leaf { hyp := 3172, conc := 3171, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3173, conc := 3172, proof := sorry })
                      (RArray.leaf { hyp := 3197, conc := 3174, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3198, conc := 3197, proof := sorry })
                      (RArray.leaf { hyp := 3201, conc := 3199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3202, conc := 3201, proof := sorry })
                      (RArray.leaf { hyp := 3206, conc := 3205, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3214, conc := 3208, proof := sorry })
                      (RArray.leaf { hyp := 3218, conc := 3216, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3219, conc := 3218, proof := sorry })
                      (RArray.leaf { hyp := 3223, conc := 3222, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 321, conc := 327, proof := sorry })
                      (RArray.leaf { hyp := 321, conc := 329, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 321, conc := 330, proof := sorry })
                      (RArray.leaf { hyp := 321, conc := 3310, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 321, conc := 3327, proof := sorry })
                      (RArray.leaf { hyp := 321, conc := 3335, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 321, conc := 3336, proof := sorry })
                      (RArray.leaf { hyp := 321, conc := 3338, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 321, conc := 3538, proof := sorry })
                      (RArray.leaf { hyp := 321, conc := 41, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3232, conc := 3225, proof := sorry })
                      (RArray.leaf { hyp := 3233, conc := 3232, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3237, conc := 3235, proof := sorry })
                      (RArray.leaf { hyp := 3238, conc := 3237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3239, conc := 3238, proof := sorry })
                      (RArray.leaf { hyp := 3242, conc := 3240, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3243, conc := 3242, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3244, conc := 3243, proof := sorry })
                      (RArray.leaf { hyp := 3248, conc := 3247, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3250, conc := 3249, proof := sorry })
                      (RArray.leaf { hyp := 3281, conc := 39, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 31, conc := 3198, proof := sorry })
                      (RArray.leaf { hyp := 3304, conc := 323, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3343, conc := 331, proof := sorry })
                      (RArray.leaf { hyp := 3355, conc := 44, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3387, conc := 4274, proof := sorry })
                      (RArray.leaf { hyp := 3391, conc := 4277, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3391, conc := 4326, proof := sorry })
                      (RArray.leaf { hyp := 3397, conc := 3720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 32, conc := 3251, proof := sorry })
                      (RArray.leaf { hyp := 3484, conc := 39, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3507, conc := 3340, proof := sorry })
                      (RArray.leaf { hyp := 34, conc := 32, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3625, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3687, conc := 39, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3688, conc := 39, proof := sorry })
                      (RArray.leaf { hyp := 3690, conc := 39, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3691, conc := 39, proof := sorry })
                      (RArray.leaf { hyp := 3698, conc := 39, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 35, conc := 34, proof := sorry })
                      (RArray.leaf { hyp := 3702, conc := 39, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3703, conc := 39, proof := sorry })
                      (RArray.leaf { hyp := 3828, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3848, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 387, conc := 38, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 387, conc := 406, proof := sorry })
                      (RArray.leaf { hyp := 387, conc := 44, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3964, conc := 390, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4031, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4093, conc := 39, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4116, conc := 41, proof := sorry })
                      (RArray.leaf { hyp := 4141, conc := 4654, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4142, conc := 4655, proof := sorry })
                      (RArray.leaf { hyp := 4167, conc := 4059, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4191, conc := 374, proof := sorry })
                      (RArray.leaf { hyp := 4196, conc := 3713, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4197, conc := 375, proof := sorry })
                      (RArray.leaf { hyp := 4203, conc := 4624, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4219, conc := 373, proof := sorry })
                      (RArray.leaf { hyp := 4234, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 41, conc := 4675, proof := sorry })
                      (RArray.leaf { hyp := 4388, conc := 4275, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 42, conc := 4676, proof := sorry })
                      (RArray.leaf { hyp := 4424, conc := 4276, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4574, conc := 4280, proof := sorry })
                      (RArray.leaf { hyp := 44, conc := 4277, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 513, conc := 36, proof := sorry })
                      (RArray.leaf { hyp := 524, conc := 518, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 533, conc := 532, proof := sorry })
                      (RArray.leaf { hyp := 534, conc := 533, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 558, conc := 535, proof := sorry })
                      (RArray.leaf { hyp := 559, conc := 558, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 562, conc := 560, proof := sorry })
                      (RArray.leaf { hyp := 563, conc := 562, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 566, conc := 564, proof := sorry })
                      (RArray.leaf { hyp := 567, conc := 566, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 568, conc := 567, proof := sorry })
                      (RArray.leaf { hyp := 575, conc := 569, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 576, conc := 575, proof := sorry })
                      (RArray.leaf { hyp := 579, conc := 577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 584, conc := 583, proof := sorry })
                      (RArray.leaf { hyp := 590, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 593, conc := 586, proof := sorry })
                      (RArray.leaf { hyp := 594, conc := 593, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 595, conc := 594, proof := sorry })
                      (RArray.leaf { hyp := 598, conc := 596, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 603, conc := 601, proof := sorry })
                      (RArray.leaf { hyp := 608, conc := 606, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 609, conc := 608, proof := sorry })
                      (RArray.leaf { hyp := 610, conc := 609, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 611, conc := 610, proof := sorry })
                      (RArray.leaf { hyp := 5, conc := 598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 716, conc := 6, proof := sorry })
                      (RArray.leaf { hyp := 720, conc := 719, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 731, conc := 729, proof := sorry })
                      (RArray.leaf { hyp := 736, conc := 735, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 741, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 761, conc := 75, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 762, conc := 761, proof := sorry })
                      (RArray.leaf { hyp := 765, conc := 763, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 766, conc := 765, proof := sorry })
                      (RArray.leaf { hyp := 75, conc := 738, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 769, conc := 76, proof := sorry })
                      (RArray.leaf { hyp := 770, conc := 769, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 771, conc := 770, proof := sorry })
                      (RArray.leaf { hyp := 778, conc := 772, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 76, conc := 767, proof := sorry })
                      (RArray.leaf { hyp := 779, conc := 778, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 782, conc := 780, proof := sorry })
                      (RArray.leaf { hyp := 783, conc := 782, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 786, conc := 784, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 787, conc := 786, proof := sorry })
                      (RArray.leaf { hyp := 788, conc := 787, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 797, conc := 796, proof := sorry })
                      (RArray.leaf { hyp := 798, conc := 797, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 78, conc := 788, proof := sorry })
                      (RArray.leaf { hyp := 799, conc := 79, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 801, conc := 799, proof := sorry })
                      (RArray.leaf { hyp := 802, conc := 801, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 803, conc := 802, proof := sorry })
                      (RArray.leaf { hyp := 806, conc := 804, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 807, conc := 806, proof := sorry })
                      (RArray.leaf { hyp := 808, conc := 807, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 79, conc := 798, proof := sorry })
                      (RArray.leaf { hyp := 809, conc := 80, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 811, conc := 809, proof := sorry })
                      (RArray.leaf { hyp := 812, conc := 811, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 813, conc := 812, proof := sorry })
                      (RArray.leaf { hyp := 86, conc := 815, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 87, conc := 86, proof := sorry })
                      (RArray.leaf { hyp := 898, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 90, conc := 88, proof := sorry })
                      (RArray.leaf { hyp := 919, conc := 91, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 91, conc := 90, proof := sorry })
                      (RArray.leaf { hyp := 930, conc := 92, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 92, conc := 924, proof := sorry })
                      (RArray.leaf { hyp := 94, conc := 941, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 964, conc := 95, proof := sorry })
                      (RArray.leaf { hyp := 968, conc := 966, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 95, conc := 94, proof := sorry })
                      (RArray.leaf { hyp := 969, conc := 96, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 978, conc := 39, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 981, conc := 97, proof := sorry })
                      (RArray.leaf { hyp := 985, conc := 983, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 990, conc := 989, proof := sorry })
                      (RArray.leaf { hyp := 999, conc := 893, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 999, conc := 930, proof := sorry })
                      (RArray.leaf { hyp := 1001, conc := 894, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1002, conc := 999, proof := sorry })
                      (RArray.leaf { hyp := 1002, conc := 1000, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1002, conc := 1001, proof := sorry })
                      (RArray.leaf { hyp := 1002, conc := 895, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1003, conc := 855, proof := sorry })
                      (RArray.leaf { hyp := 1003, conc := 929, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1003, conc := 950, proof := sorry })
                      (RArray.leaf { hyp := 1003, conc := 984, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1004, conc := 968, proof := sorry })
                      (RArray.leaf { hyp := 1004, conc := 985, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1005, conc := 888, proof := sorry })
                      (RArray.leaf { hyp := 1005, conc := 952, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1005, conc := 969, proof := sorry })
                      (RArray.leaf { hyp := 1005, conc := 986, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1006, conc := 890, proof := sorry })
                      (RArray.leaf { hyp := 1007, conc := 1004, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1007, conc := 891, proof := sorry })
                      (RArray.leaf { hyp := 1007, conc := 953, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1007, conc := 970, proof := sorry })
                      (RArray.leaf { hyp := 1008, conc := 942, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1011, conc := 898, proof := sorry })
                      (RArray.leaf { hyp := 1012, conc := 1009, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1012, conc := 899, proof := sorry })
                      (RArray.leaf { hyp := 1013, conc := 1003, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1013, conc := 1008, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1013, conc := 900, proof := sorry })
                      (RArray.leaf { hyp := 1013, conc := 988, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1013, conc := 998, proof := sorry })
                      (RArray.leaf { hyp := 1014, conc := 999, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1014, conc := 901, proof := sorry })
                      (RArray.leaf { hyp := 1016, conc := 902, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1017, conc := 903, proof := sorry })
                      (RArray.leaf { hyp := 1017, conc := 974, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1018, conc := 1002, proof := sorry })
                      (RArray.leaf { hyp := 1018, conc := 1012, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1018, conc := 1014, proof := sorry })
                      (RArray.leaf { hyp := 1018, conc := 1015, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1018, conc := 1016, proof := sorry })
                      (RArray.leaf { hyp := 1018, conc := 1017, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1018, conc := 904, proof := sorry })
                      (RArray.leaf { hyp := 1020, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1021, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1022, conc := 1019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1023, conc := 1020, proof := sorry })
                      (RArray.leaf { hyp := 1025, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1026, conc := 1024, proof := sorry })
                      (RArray.leaf { hyp := 1026, conc := 1025, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1027, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1028, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1030, conc := 1021, proof := sorry })
                      (RArray.leaf { hyp := 1030, conc := 1024, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1030, conc := 1027, proof := sorry })
                      (RArray.leaf { hyp := 1031, conc := 1021, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1031, conc := 1025, proof := sorry })
                      (RArray.leaf { hyp := 1032, conc := 1024, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1033, conc := 1026, proof := sorry })
                      (RArray.leaf { hyp := 1033, conc := 1029, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1033, conc := 1032, proof := sorry })
                      (RArray.leaf { hyp := 1034, conc := 1019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1035, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1037, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1038, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1040, conc := 1021, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1040, conc := 1034, proof := sorry })
                      (RArray.leaf { hyp := 1040, conc := 1037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1041, conc := 1021, proof := sorry })
                      (RArray.leaf { hyp := 1041, conc := 1038, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1043, conc := 1039, proof := sorry })
                      (RArray.leaf { hyp := 1044, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1045, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1047, conc := 1019, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1048, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1049, conc := 1020, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1049, conc := 1047, proof := sorry })
                      (RArray.leaf { hyp := 1049, conc := 1048, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1050, conc := 1021, proof := sorry })
                      (RArray.leaf { hyp := 1050, conc := 1044, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1050, conc := 1047, proof := sorry })
                      (RArray.leaf { hyp := 1051, conc := 1021, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1051, conc := 1045, proof := sorry })
                      (RArray.leaf { hyp := 1051, conc := 1048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1052, conc := 1022, proof := sorry })
                      (RArray.leaf { hyp := 1052, conc := 1044, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1053, conc := 1046, proof := sorry })
                      (RArray.leaf { hyp := 1054, conc := 1024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1054, conc := 1034, proof := sorry })
                      (RArray.leaf { hyp := 1054, conc := 1044, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1055, conc := 1024, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1055, conc := 1045, proof := sorry })
                      (RArray.leaf { hyp := 1057, conc := 1056, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 104, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1059, conc := 1024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1059, conc := 1038, proof := sorry })
                      (RArray.leaf { hyp := 1060, conc := 1025, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1060, conc := 1037, proof := sorry })
                      (RArray.leaf { hyp := 1060, conc := 1048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1061, conc := 1039, proof := sorry })
                      (RArray.leaf { hyp := 1062, conc := 1027, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1062, conc := 1034, proof := sorry })
                      (RArray.leaf { hyp := 1062, conc := 1047, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1063, conc := 1027, proof := sorry })
                      (RArray.leaf { hyp := 1063, conc := 1035, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1063, conc := 1048, proof := sorry })
                      (RArray.leaf { hyp := 1065, conc := 1036, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1065, conc := 1049, proof := sorry })
                      (RArray.leaf { hyp := 1065, conc := 1064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1066, conc := 1040, proof := sorry })
                      (RArray.leaf { hyp := 1066, conc := 1050, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1066, conc := 1054, proof := sorry })
                      (RArray.leaf { hyp := 1066, conc := 1058, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1066, conc := 1062, proof := sorry })
                      (RArray.leaf { hyp := 1067, conc := 1041, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 1051, proof := sorry })
                      (RArray.leaf { hyp := 1067, conc := 1055, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1067, conc := 1059, proof := sorry })
                      (RArray.leaf { hyp := 1068, conc := 1060, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1068, conc := 1064, proof := sorry })
                      (RArray.leaf { hyp := 1069, conc := 1042, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1069, conc := 1064, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1070, conc := 1043, proof := sorry })
                      (RArray.leaf { hyp := 1070, conc := 1053, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1070, conc := 1057, proof := sorry })
                      (RArray.leaf { hyp := 1070, conc := 1061, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1070, conc := 1065, proof := sorry })
                      (RArray.leaf { hyp := 1070, conc := 1068, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1070, conc := 1069, proof := sorry })
                      (RArray.leaf { hyp := 1074, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1075, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1077, conc := 1071, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 106, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1080, conc := 1076, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1080, conc := 1078, proof := sorry })
                      (RArray.leaf { hyp := 1080, conc := 1079, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1081, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1082, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1084, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1085, conc := 1019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 107, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1090, conc := 1086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1090, conc := 1088, proof := sorry })
                      (RArray.leaf { hyp := 1091, conc := 1071, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1094, conc := 1073, proof := sorry })
                      (RArray.leaf { hyp := 1094, conc := 1083, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1094, conc := 1092, proof := sorry })
                      (RArray.leaf { hyp := 1094, conc := 1093, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1097, conc := 1025, proof := sorry })
                      (RArray.leaf { hyp := 1098, conc := 1086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1098, conc := 1096, proof := sorry })
                      (RArray.leaf { hyp := 1099, conc := 1071, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1100, conc := 1027, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1100, conc := 1072, proof := sorry })
                      (RArray.leaf { hyp := 1102, conc := 1086, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1102, conc := 1101, proof := sorry })
                      (RArray.leaf { hyp := 1103, conc := 1077, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1103, conc := 1091, proof := sorry })
                      (RArray.leaf { hyp := 1103, conc := 1099, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1104, conc := 1096, proof := sorry })
                      (RArray.leaf { hyp := 1105, conc := 1101, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1106, conc := 1101, proof := sorry })
                      (RArray.leaf { hyp := 1107, conc := 1080, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1107, conc := 1090, proof := sorry })
                      (RArray.leaf { hyp := 1107, conc := 1098, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1107, conc := 1102, proof := sorry })
                      (RArray.leaf { hyp := 1107, conc := 1104, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1107, conc := 1105, proof := sorry })
                      (RArray.leaf { hyp := 1107, conc := 1106, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1108, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1109, conc := 1019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1111, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 1112, conc := 1019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1116, conc := 1022, proof := sorry })
                      (RArray.leaf { hyp := 1116, conc := 1108, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1116, conc := 1112, proof := sorry })
                      (RArray.leaf { hyp := 1117, conc := 1113, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1117, conc := 1115, proof := sorry })
                      (RArray.leaf { hyp := 1121, conc := 1019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1127, conc := 1123, proof := sorry })
                      (RArray.leaf { hyp := 1127, conc := 1125, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1127, conc := 1126, proof := sorry })
                      (RArray.leaf { hyp := 1130, conc := 1025, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1131, conc := 1110, proof := sorry })
                      (RArray.leaf { hyp := 1131, conc := 1120, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1131, conc := 1129, proof := sorry })
                      (RArray.leaf { hyp := 1132, conc := 1024, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1132, conc := 1111, proof := sorry })
                      (RArray.leaf { hyp := 1135, conc := 1133, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1135, conc := 1134, proof := sorry })
                      (RArray.leaf { hyp := 1136, conc := 1027, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1136, conc := 1108, proof := sorry })
                      (RArray.leaf { hyp := 1137, conc := 1109, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 112, conc := 111, proof := sorry })
                      (RArray.leaf { hyp := 1139, conc := 1137, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1139, conc := 1138, proof := sorry })
                      (RArray.leaf { hyp := 1140, conc := 1114, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1144, conc := 1117, proof := sorry })
                      (RArray.leaf { hyp := 1144, conc := 1127, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1144, conc := 1135, proof := sorry })
                      (RArray.leaf { hyp := 1144, conc := 1139, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1144, conc := 1141, proof := sorry })
                      (RArray.leaf { hyp := 1144, conc := 1142, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1144, conc := 1143, proof := sorry })
                      (RArray.leaf { hyp := 1145, conc := 1071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1148, conc := 1146, proof := sorry })
                      (RArray.leaf { hyp := 1148, conc := 1147, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1151, conc := 1035, proof := sorry })
                      (RArray.leaf { hyp := 1151, conc := 1074, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1151, conc := 1112, proof := sorry })
                      (RArray.leaf { hyp := 1152, conc := 1150, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1153, conc := 1071, proof := sorry })
                      (RArray.leaf { hyp := 1154, conc := 1037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1154, conc := 1072, proof := sorry })
                      (RArray.leaf { hyp := 1154, conc := 1112, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1156, conc := 1155, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1157, conc := 1149, proof := sorry })
                      (RArray.leaf { hyp := 1157, conc := 1153, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1158, conc := 1150, proof := sorry })
                      (RArray.leaf { hyp := 114, conc := 98, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1159, conc := 1155, proof := sorry })
                      (RArray.leaf { hyp := 1160, conc := 1155, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1161, conc := 1152, proof := sorry })
                      (RArray.leaf { hyp := 1161, conc := 1156, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1161, conc := 1158, proof := sorry })
                      (RArray.leaf { hyp := 1161, conc := 1159, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1161, conc := 1160, proof := sorry })
                      (RArray.leaf { hyp := 1162, conc := 1118, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1165, conc := 1163, proof := sorry })
                      (RArray.leaf { hyp := 1169, conc := 1086, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1169, conc := 1167, proof := sorry })
                      (RArray.leaf { hyp := 1169, conc := 1168, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1171, conc := 1082, proof := sorry })
                      (RArray.leaf { hyp := 1173, conc := 1171, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1173, conc := 1172, proof := sorry })
                      (RArray.leaf { hyp := 1174, conc := 1124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1174, conc := 1162, proof := sorry })
                      (RArray.leaf { hyp := 1175, conc := 1171, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1178, conc := 1169, proof := sorry })
                      (RArray.leaf { hyp := 1178, conc := 1173, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1178, conc := 1175, proof := sorry })
                      (RArray.leaf { hyp := 1178, conc := 1176, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1178, conc := 1177, proof := sorry })
                      (RArray.leaf { hyp := 116, conc := 98, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1179, conc := 1071, proof := sorry })
                      (RArray.leaf { hyp := 1182, conc := 1181, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1183, conc := 1044, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1183, conc := 1074, proof := sorry })
                      (RArray.leaf { hyp := 1183, conc := 1121, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1184, conc := 1075, proof := sorry })
                      (RArray.leaf { hyp := 1186, conc := 1184, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1186, conc := 1185, proof := sorry })
                      (RArray.leaf { hyp := 1187, conc := 1071, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 117, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1190, conc := 1188, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1190, conc := 1189, proof := sorry })
                      (RArray.leaf { hyp := 1191, conc := 1179, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1191, conc := 1187, proof := sorry })
                      (RArray.leaf { hyp := 1192, conc := 1184, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1194, conc := 1184, proof := sorry })
                      (RArray.leaf { hyp := 1195, conc := 1186, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1195, conc := 1190, proof := sorry })
                      (RArray.leaf { hyp := 1195, conc := 1192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1195, conc := 1193, proof := sorry })
                      (RArray.leaf { hyp := 1195, conc := 1194, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1196, conc := 1128, proof := sorry })
                      (RArray.leaf { hyp := 1196, conc := 1179, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1197, conc := 1146, proof := sorry })
                      (RArray.leaf { hyp := 1198, conc := 1147, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1199, conc := 1181, proof := sorry })
                      (RArray.leaf { hyp := 1200, conc := 1094, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1200, conc := 1131, proof := sorry })
                      (RArray.leaf { hyp := 1200, conc := 1148, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1200, conc := 1165, proof := sorry })
                      (RArray.leaf { hyp := 1200, conc := 1182, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1200, conc := 1197, proof := sorry })
                      (RArray.leaf { hyp := 1200, conc := 1198, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1200, conc := 1199, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1201, conc := 1054, proof := sorry })
                      (RArray.leaf { hyp := 1201, conc := 1149, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1202, conc := 1150, proof := sorry })
                      (RArray.leaf { hyp := 1205, conc := 1202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1205, conc := 1203, proof := sorry })
                      (RArray.leaf { hyp := 1205, conc := 1204, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1206, conc := 1058, proof := sorry })
                      (RArray.leaf { hyp := 1206, conc := 1187, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1208, conc := 1155, proof := sorry })
                      (RArray.leaf { hyp := 1210, conc := 1207, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1210, conc := 1208, proof := sorry })
                      (RArray.leaf { hyp := 1210, conc := 1209, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1211, conc := 1099, proof := sorry })
                      (RArray.leaf { hyp := 1211, conc := 1136, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1215, conc := 1212, proof := sorry })
                      (RArray.leaf { hyp := 1215, conc := 1213, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1215, conc := 1214, proof := sorry })
                      (RArray.leaf { hyp := 1216, conc := 1103, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1216, conc := 1157, proof := sorry })
                      (RArray.leaf { hyp := 1216, conc := 1191, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1216, conc := 1196, proof := sorry })
                      (RArray.leaf { hyp := 1216, conc := 1206, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1216, conc := 1211, proof := sorry })
                      (RArray.leaf { hyp := 1217, conc := 1212, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1218, conc := 1208, proof := sorry })
                      (RArray.leaf { hyp := 1220, conc := 1208, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1144, proof := sorry })
                      (RArray.leaf { hyp := 1221, conc := 1161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1178, proof := sorry })
                      (RArray.leaf { hyp := 1221, conc := 1195, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1205, proof := sorry })
                      (RArray.leaf { hyp := 1221, conc := 1210, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1215, proof := sorry })
                      (RArray.leaf { hyp := 1221, conc := 1217, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1218, proof := sorry })
                      (RArray.leaf { hyp := 1221, conc := 1219, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1221, conc := 1220, proof := sorry })
                      (RArray.leaf { hyp := 1223, conc := 1222, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1224, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1225, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1226, conc := 1223, proof := sorry })
                      (RArray.leaf { hyp := 1226, conc := 1224, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1226, conc := 1225, proof := sorry })
                      (RArray.leaf { hyp := 1227, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1228, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1229, conc := 1223, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1229, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1229, conc := 1228, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1230, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1232, conc := 1230, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1232, conc := 1231, proof := sorry })
                      (RArray.leaf { hyp := 1233, conc := 1224, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1233, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1233, conc := 1230, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1234, conc := 1228, proof := sorry })
                      (RArray.leaf { hyp := 1234, conc := 1231, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1235, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1235, conc := 1231, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1236, conc := 1229, proof := sorry })
                      (RArray.leaf { hyp := 1236, conc := 1232, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1236, conc := 1233, proof := sorry })
                      (RArray.leaf { hyp := 1236, conc := 1234, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1236, conc := 1235, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1237, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1238, conc := 1222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 122, conc := 118, proof := sorry })
                      (RArray.leaf { hyp := 122, conc := 120, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 122, conc := 121, proof := sorry })
                      (RArray.leaf { hyp := 1239, conc := 1223, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1239, conc := 1238, proof := sorry })
                      (RArray.leaf { hyp := 1240, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1241, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1242, conc := 1223, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1242, conc := 1240, proof := sorry })
                      (RArray.leaf { hyp := 1242, conc := 1241, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1243, conc := 1224, proof := sorry })
                      (RArray.leaf { hyp := 1243, conc := 1240, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1244, conc := 1224, proof := sorry })
                      (RArray.leaf { hyp := 1244, conc := 1238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1244, conc := 1241, proof := sorry })
                      (RArray.leaf { hyp := 1246, conc := 1226, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1246, conc := 1239, proof := sorry })
                      (RArray.leaf { hyp := 1246, conc := 1242, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1246, conc := 1244, proof := sorry })
                      (RArray.leaf { hyp := 1246, conc := 1245, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1247, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1248, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 123, conc := 98, proof := sorry })
                      (RArray.leaf { hyp := 1249, conc := 1223, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1249, conc := 1247, proof := sorry })
                      (RArray.leaf { hyp := 1249, conc := 1248, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1250, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1251, conc := 1222, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1252, conc := 1223, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1252, conc := 1250, proof := sorry })
                      (RArray.leaf { hyp := 1252, conc := 1251, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1253, conc := 1224, proof := sorry })
                      (RArray.leaf { hyp := 1253, conc := 1247, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1253, conc := 1250, proof := sorry })
                      (RArray.leaf { hyp := 1254, conc := 1224, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1254, conc := 1248, proof := sorry })
                      (RArray.leaf { hyp := 1255, conc := 1225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1255, conc := 1247, proof := sorry })
                      (RArray.leaf { hyp := 1255, conc := 1251, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1256, conc := 1226, proof := sorry })
                      (RArray.leaf { hyp := 1256, conc := 1249, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1256, conc := 1253, proof := sorry })
                      (RArray.leaf { hyp := 1256, conc := 1254, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1256, conc := 1255, proof := sorry })
                      (RArray.leaf { hyp := 1257, conc := 1227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1257, conc := 1237, proof := sorry })
                      (RArray.leaf { hyp := 1257, conc := 1247, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1258, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1258, conc := 1238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1258, conc := 1248, proof := sorry })
                      (RArray.leaf { hyp := 1260, conc := 1229, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1260, conc := 1249, proof := sorry })
                      (RArray.leaf { hyp := 1260, conc := 1258, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1260, conc := 1259, proof := sorry })
                      (RArray.leaf { hyp := 1261, conc := 1227, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1261, conc := 1240, proof := sorry })
                      (RArray.leaf { hyp := 1261, conc := 1250, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1262, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 1262, conc := 1241, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1263, conc := 1228, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1263, conc := 1240, proof := sorry })
                      (RArray.leaf { hyp := 1266, conc := 1230, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1266, conc := 1238, proof := sorry })
                      (RArray.leaf { hyp := 1268, conc := 1267, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1269, conc := 1233, proof := sorry })
                      (RArray.leaf { hyp := 1269, conc := 1243, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1269, conc := 1253, proof := sorry })
                      (RArray.leaf { hyp := 1269, conc := 1261, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1269, conc := 1265, proof := sorry })
                      (RArray.leaf { hyp := 1270, conc := 1233, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1270, conc := 1244, proof := sorry })
                      (RArray.leaf { hyp := 1270, conc := 1258, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1270, conc := 1266, proof := sorry })
                      (RArray.leaf { hyp := 1271, conc := 1267, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1272, conc := 1267, proof := sorry })
                      (RArray.leaf { hyp := 1273, conc := 1268, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1273, conc := 1270, proof := sorry })
                      (RArray.leaf { hyp := 1273, conc := 1271, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1275, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1277, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1278, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1280, conc := 1274, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1283, conc := 1282, proof := sorry })
                      (RArray.leaf { hyp := 1284, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1285, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1287, conc := 1222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1288, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1293, conc := 1286, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1294, conc := 1274, proof := sorry })
                      (RArray.leaf { hyp := 1297, conc := 1276, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1297, conc := 1296, proof := sorry })
                      (RArray.leaf { hyp := 128, conc := 127, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 11, conc := 9, proof := sorry })
                      (RArray.leaf { hyp := 1300, conc := 1228, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1300, conc := 1277, proof := sorry })
                      (RArray.leaf { hyp := 1301, conc := 1299, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1302, conc := 1274, proof := sorry })
                      (RArray.leaf { hyp := 1305, conc := 1304, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1306, conc := 1280, proof := sorry })
                      (RArray.leaf { hyp := 1306, conc := 1302, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1307, conc := 1299, proof := sorry })
                      (RArray.leaf { hyp := 1308, conc := 1304, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1309, conc := 1304, proof := sorry })
                      (RArray.leaf { hyp := 1310, conc := 1305, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1310, conc := 1307, proof := sorry })
                      (RArray.leaf { hyp := 1310, conc := 1308, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1310, conc := 1309, proof := sorry })
                      (RArray.leaf { hyp := 1311, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1312, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1314, conc := 1222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1315, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 130, conc := 127, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1319, conc := 1225, proof := sorry })
                      (RArray.leaf { hyp := 1320, conc := 1318, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1321, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1322, conc := 1222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1324, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 1326, conc := 1325, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1327, conc := 1321, proof := sorry })
                      (RArray.leaf { hyp := 1328, conc := 1325, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 131, conc := 127, proof := sorry })
                      (RArray.leaf { hyp := 1330, conc := 1329, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1334, conc := 1313, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1334, conc := 1323, proof := sorry })
                      (RArray.leaf { hyp := 1338, conc := 1336, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1338, conc := 1337, proof := sorry })
                      (RArray.leaf { hyp := 132, conc := 125, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 132, conc := 128, proof := sorry })
                      (RArray.leaf { hyp := 132, conc := 130, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 132, conc := 131, proof := sorry })
                      (RArray.leaf { hyp := 1339, conc := 1230, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1339, conc := 1311, proof := sorry })
                      (RArray.leaf { hyp := 1339, conc := 1324, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1340, conc := 1312, proof := sorry })
                      (RArray.leaf { hyp := 1342, conc := 1340, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1342, conc := 1341, proof := sorry })
                      (RArray.leaf { hyp := 1343, conc := 1317, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1347, conc := 1320, proof := sorry })
                      (RArray.leaf { hyp := 1347, conc := 1338, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1347, conc := 1342, proof := sorry })
                      (RArray.leaf { hyp := 1347, conc := 1344, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1347, conc := 1345, proof := sorry })
                      (RArray.leaf { hyp := 1347, conc := 1346, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1348, conc := 1274, proof := sorry })
                      (RArray.leaf { hyp := 133, conc := 123, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1351, conc := 1349, proof := sorry })
                      (RArray.leaf { hyp := 1352, conc := 1237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1352, conc := 1277, proof := sorry })
                      (RArray.leaf { hyp := 1352, conc := 1314, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1353, conc := 1278, proof := sorry })
                      (RArray.leaf { hyp := 1354, conc := 1238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1355, conc := 1353, proof := sorry })
                      (RArray.leaf { hyp := 1356, conc := 1274, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1357, conc := 1240, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1357, conc := 1275, proof := sorry })
                      (RArray.leaf { hyp := 1359, conc := 1358, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1360, conc := 1356, proof := sorry })
                      (RArray.leaf { hyp := 1361, conc := 1353, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1362, conc := 1358, proof := sorry })
                      (RArray.leaf { hyp := 1363, conc := 1358, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1364, conc := 1359, proof := sorry })
                      (RArray.leaf { hyp := 1364, conc := 1361, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1364, conc := 1362, proof := sorry })
                      (RArray.leaf { hyp := 1364, conc := 1363, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1367, conc := 1238, proof := sorry })
                      (RArray.leaf { hyp := 1367, conc := 1284, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1367, conc := 1322, proof := sorry })
                      (RArray.leaf { hyp := 1368, conc := 1323, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1368, conc := 1366, proof := sorry })
                      (RArray.leaf { hyp := 135, conc := 124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1369, conc := 1237, proof := sorry })
                      (RArray.leaf { hyp := 1369, conc := 1287, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1372, conc := 1370, proof := sorry })
                      (RArray.leaf { hyp := 1372, conc := 1371, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1373, conc := 1240, proof := sorry })
                      (RArray.leaf { hyp := 1373, conc := 1284, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1374, conc := 1285, proof := sorry })
                      (RArray.leaf { hyp := 1376, conc := 1374, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1376, conc := 1375, proof := sorry })
                      (RArray.leaf { hyp := 1377, conc := 1290, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1377, conc := 1327, proof := sorry })
                      (RArray.leaf { hyp := 1377, conc := 1365, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 136, conc := 134, proof := sorry })
                      (RArray.leaf { hyp := 136, conc := 135, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1381, conc := 1330, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1381, conc := 1372, proof := sorry })
                      (RArray.leaf { hyp := 1381, conc := 1376, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1381, conc := 1378, proof := sorry })
                      (RArray.leaf { hyp := 1381, conc := 1379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1381, conc := 1380, proof := sorry })
                      (RArray.leaf { hyp := 1382, conc := 1274, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1383, conc := 1322, proof := sorry })
                      (RArray.leaf { hyp := 1385, conc := 1323, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1385, conc := 1384, proof := sorry })
                      (RArray.leaf { hyp := 1386, conc := 1247, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1386, conc := 1277, proof := sorry })
                      (RArray.leaf { hyp := 1390, conc := 1274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1393, conc := 1391, proof := sorry })
                      (RArray.leaf { hyp := 1393, conc := 1392, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1394, conc := 1390, proof := sorry })
                      (RArray.leaf { hyp := 1398, conc := 1283, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1398, conc := 1389, proof := sorry })
                      (RArray.leaf { hyp := 1398, conc := 1393, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1398, conc := 1395, proof := sorry })
                      (RArray.leaf { hyp := 1398, conc := 1396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1398, conc := 1397, proof := sorry })
                      (RArray.leaf { hyp := 1399, conc := 1294, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1399, conc := 1348, proof := sorry })
                      (RArray.leaf { hyp := 1399, conc := 1382, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1400, conc := 1332, proof := sorry })
                      (RArray.leaf { hyp := 1400, conc := 1349, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1401, conc := 1350, proof := sorry })
                      (RArray.leaf { hyp := 1402, conc := 1366, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1403, conc := 1297, proof := sorry })
                      (RArray.leaf { hyp := 1403, conc := 1334, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1403, conc := 1351, proof := sorry })
                      (RArray.leaf { hyp := 1403, conc := 1385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1403, conc := 1401, proof := sorry })
                      (RArray.leaf { hyp := 1403, conc := 1402, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1404, conc := 1257, proof := sorry })
                      (RArray.leaf { hyp := 1404, conc := 1298, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1404, conc := 1352, proof := sorry })
                      (RArray.leaf { hyp := 1408, conc := 1301, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1408, conc := 1355, proof := sorry })
                      (RArray.leaf { hyp := 1408, conc := 1405, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1408, conc := 1406, proof := sorry })
                      (RArray.leaf { hyp := 1408, conc := 1407, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1409, conc := 1390, proof := sorry })
                      (RArray.leaf { hyp := 1413, conc := 1410, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1413, conc := 1411, proof := sorry })
                      (RArray.leaf { hyp := 1413, conc := 1412, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1414, conc := 1390, proof := sorry })
                      (RArray.leaf { hyp := 1418, conc := 1415, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1418, conc := 1416, proof := sorry })
                      (RArray.leaf { hyp := 1418, conc := 1417, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 140, conc := 138, proof := sorry })
                      (RArray.leaf { hyp := 140, conc := 139, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1419, conc := 1306, proof := sorry })
                      (RArray.leaf { hyp := 1419, conc := 1343, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1419, conc := 1360, proof := sorry })
                      (RArray.leaf { hyp := 1419, conc := 1394, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1419, conc := 1409, proof := sorry })
                      (RArray.leaf { hyp := 1419, conc := 1414, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1424, conc := 1310, proof := sorry })
                      (RArray.leaf { hyp := 1424, conc := 1364, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1424, conc := 1413, proof := sorry })
                      (RArray.leaf { hyp := 1424, conc := 1418, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1424, conc := 1420, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1424, conc := 1421, proof := sorry })
                      (RArray.leaf { hyp := 1424, conc := 1422, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1424, conc := 1423, proof := sorry })
                      (RArray.leaf { hyp := 1426, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1427, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1428, conc := 1425, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1429, conc := 1426, proof := sorry })
                      (RArray.leaf { hyp := 1429, conc := 1427, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1429, conc := 1428, proof := sorry })
                      (RArray.leaf { hyp := 1430, conc := 1425, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1431, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1433, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1434, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1436, conc := 1427, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1436, conc := 1430, proof := sorry })
                      (RArray.leaf { hyp := 1436, conc := 1433, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1439, conc := 1432, proof := sorry })
                      (RArray.leaf { hyp := 1440, conc := 1425, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1441, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1442, conc := 1426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1442, conc := 1440, proof := sorry })
                      (RArray.leaf { hyp := 1442, conc := 1441, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1443, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1444, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1445, conc := 1443, proof := sorry })
                      (RArray.leaf { hyp := 1446, conc := 1427, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1446, conc := 1440, proof := sorry })
                      (RArray.leaf { hyp := 1446, conc := 1443, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1449, conc := 1448, proof := sorry })
                      (RArray.leaf { hyp := 1450, conc := 1425, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1452, conc := 1426, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1452, conc := 1450, proof := sorry })
                      (RArray.leaf { hyp := 1452, conc := 1451, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1453, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1454, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1456, conc := 1427, proof := sorry })
                      (RArray.leaf { hyp := 1456, conc := 1450, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1456, conc := 1453, proof := sorry })
                      (RArray.leaf { hyp := 1458, conc := 1428, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1458, conc := 1450, proof := sorry })
                      (RArray.leaf { hyp := 1458, conc := 1454, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 144, conc := 142, proof := sorry })
                      (RArray.leaf { hyp := 144, conc := 143, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1459, conc := 1457, proof := sorry })
                      (RArray.leaf { hyp := 1460, conc := 1430, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1460, conc := 1450, proof := sorry })
                      (RArray.leaf { hyp := 1463, conc := 1461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1463, conc := 1462, proof := sorry })
                      (RArray.leaf { hyp := 1466, conc := 1431, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1466, conc := 1443, proof := sorry })
                      (RArray.leaf { hyp := 1467, conc := 1432, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1468, conc := 1433, proof := sorry })
                      (RArray.leaf { hyp := 1468, conc := 1440, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1468, conc := 1453, proof := sorry })
                      (RArray.leaf { hyp := 145, conc := 119, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 145, conc := 133, proof := sorry })
                      (RArray.leaf { hyp := 145, conc := 141, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1469, conc := 1433, proof := sorry })
                      (RArray.leaf { hyp := 1469, conc := 1441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1471, conc := 1442, proof := sorry })
                      (RArray.leaf { hyp := 1471, conc := 1470, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1472, conc := 1436, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1472, conc := 1456, proof := sorry })
                      (RArray.leaf { hyp := 1472, conc := 1460, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1472, conc := 1464, proof := sorry })
                      (RArray.leaf { hyp := 1472, conc := 1468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1473, conc := 1447, proof := sorry })
                      (RArray.leaf { hyp := 1473, conc := 1461, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1474, conc := 1457, proof := sorry })
                      (RArray.leaf { hyp := 1474, conc := 1466, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1474, conc := 1470, proof := sorry })
                      (RArray.leaf { hyp := 1475, conc := 1438, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1476, conc := 1439, proof := sorry })
                      (RArray.leaf { hyp := 1476, conc := 1463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1476, conc := 1471, proof := sorry })
                      (RArray.leaf { hyp := 1476, conc := 1472, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1476, conc := 1473, proof := sorry })
                      (RArray.leaf { hyp := 1476, conc := 1474, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1476, conc := 1475, proof := sorry })
                      (RArray.leaf { hyp := 1477, conc := 1425, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1478, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1479, conc := 1426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1479, conc := 1477, proof := sorry })
                      (RArray.leaf { hyp := 1479, conc := 1478, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1480, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1481, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1482, conc := 1480, proof := sorry })
                      (RArray.leaf { hyp := 1482, conc := 1481, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1483, conc := 1427, proof := sorry })
                      (RArray.leaf { hyp := 1483, conc := 1477, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1483, conc := 1480, proof := sorry })
                      (RArray.leaf { hyp := 1485, conc := 1428, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1485, conc := 1477, proof := sorry })
                      (RArray.leaf { hyp := 1485, conc := 1481, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1486, conc := 1429, proof := sorry })
                      (RArray.leaf { hyp := 1486, conc := 1479, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1486, conc := 1483, proof := sorry })
                      (RArray.leaf { hyp := 1486, conc := 1485, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1487, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1488, conc := 1425, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1490, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1492, conc := 1490, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1495, conc := 1487, proof := sorry })
                      (RArray.leaf { hyp := 1495, conc := 1491, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1496, conc := 1489, proof := sorry })
                      (RArray.leaf { hyp := 1496, conc := 1492, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1496, conc := 1494, proof := sorry })
                      (RArray.leaf { hyp := 13, conc := 7, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1500, conc := 1489, proof := sorry })
                      (RArray.leaf { hyp := 1500, conc := 1499, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1503, conc := 1431, proof := sorry })
                      (RArray.leaf { hyp := 1503, conc := 1480, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1503, conc := 1491, proof := sorry })
                      (RArray.leaf { hyp := 1504, conc := 1502, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1505, conc := 1490, proof := sorry })
                      (RArray.leaf { hyp := 1508, conc := 1507, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 149, conc := 122, proof := sorry })
                      (RArray.leaf { hyp := 149, conc := 132, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 149, conc := 136, proof := sorry })
                      (RArray.leaf { hyp := 149, conc := 140, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 149, conc := 144, proof := sorry })
                      (RArray.leaf { hyp := 149, conc := 146, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 149, conc := 147, proof := sorry })
                      (RArray.leaf { hyp := 149, conc := 148, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1509, conc := 1483, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1509, conc := 1501, proof := sorry })
                      (RArray.leaf { hyp := 1510, conc := 1498, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1511, conc := 1499, proof := sorry })
                      (RArray.leaf { hyp := 1512, conc := 1507, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1513, conc := 1439, proof := sorry })
                      (RArray.leaf { hyp := 1513, conc := 1496, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1513, conc := 1511, proof := sorry })
                      (RArray.leaf { hyp := 1514, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1515, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1517, conc := 1425, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1518, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1522, conc := 1428, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1522, conc := 1514, proof := sorry })
                      (RArray.leaf { hyp := 1522, conc := 1518, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1523, conc := 1519, proof := sorry })
                      (RArray.leaf { hyp := 1523, conc := 1521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1524, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 1525, conc := 1425, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1527, conc := 1425, proof := sorry })
                      (RArray.leaf { hyp := 151, conc := 150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1533, conc := 1526, proof := sorry })
                      (RArray.leaf { hyp := 1533, conc := 1529, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1533, conc := 1531, proof := sorry })
                      (RArray.leaf { hyp := 1533, conc := 1532, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1537, conc := 1535, proof := sorry })
                      (RArray.leaf { hyp := 152, conc := 150, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1541, conc := 1539, proof := sorry })
                      (RArray.leaf { hyp := 1541, conc := 1540, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1542, conc := 1514, proof := sorry })
                      (RArray.leaf { hyp := 1543, conc := 1515, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1545, conc := 1543, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1545, conc := 1544, proof := sorry })
                      (RArray.leaf { hyp := 1546, conc := 1520, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1547, conc := 1535, proof := sorry })
                      (RArray.leaf { hyp := 1550, conc := 1523, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1550, conc := 1533, proof := sorry })
                      (RArray.leaf { hyp := 1550, conc := 1537, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1550, conc := 1541, proof := sorry })
                      (RArray.leaf { hyp := 1550, conc := 1545, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1550, conc := 1547, proof := sorry })
                      (RArray.leaf { hyp := 1550, conc := 1548, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1550, conc := 1549, proof := sorry })
                      (RArray.leaf { hyp := 1554, conc := 1516, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1554, conc := 1552, proof := sorry })
                      (RArray.leaf { hyp := 1554, conc := 1553, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1557, conc := 1441, proof := sorry })
                      (RArray.leaf { hyp := 1558, conc := 1556, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1559, conc := 1517, proof := sorry })
                      (RArray.leaf { hyp := 1560, conc := 1478, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1562, conc := 1561, proof := sorry })
                      (RArray.leaf { hyp := 1563, conc := 1551, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1563, conc := 1555, proof := sorry })
                      (RArray.leaf { hyp := 1564, conc := 1521, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1565, conc := 1553, proof := sorry })
                      (RArray.leaf { hyp := 1566, conc := 1561, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1567, conc := 1558, proof := sorry })
                      (RArray.leaf { hyp := 1567, conc := 1562, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1567, conc := 1564, proof := sorry })
                      (RArray.leaf { hyp := 1567, conc := 1565, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1567, conc := 1566, proof := sorry })
                      (RArray.leaf { hyp := 155, conc := 150, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1571, conc := 1489, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1571, conc := 1570, proof := sorry })
                      (RArray.leaf { hyp := 1575, conc := 1573, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1575, conc := 1574, proof := sorry })
                      (RArray.leaf { hyp := 1576, conc := 1443, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1576, conc := 1487, proof := sorry })
                      (RArray.leaf { hyp := 1577, conc := 1488, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1579, conc := 1577, proof := sorry })
                      (RArray.leaf { hyp := 1579, conc := 1578, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1580, conc := 1568, proof := sorry })
                      (RArray.leaf { hyp := 1580, conc := 1572, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1581, conc := 1573, proof := sorry })
                      (RArray.leaf { hyp := 1583, conc := 1573, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1584, conc := 1496, proof := sorry })
                      (RArray.leaf { hyp := 1584, conc := 1571, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1584, conc := 1575, proof := sorry })
                      (RArray.leaf { hyp := 1584, conc := 1579, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1584, conc := 1581, proof := sorry })
                      (RArray.leaf { hyp := 1584, conc := 1582, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1584, conc := 1583, proof := sorry })
                      (RArray.leaf { hyp := 1585, conc := 1450, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1585, conc := 1477, proof := sorry })
                      (RArray.leaf { hyp := 1585, conc := 1524, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1586, conc := 1450, proof := sorry })
                      (RArray.leaf { hyp := 1586, conc := 1478, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1588, conc := 1526, proof := sorry })
                      (RArray.leaf { hyp := 1589, conc := 1450, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1589, conc := 1480, proof := sorry })
                      (RArray.leaf { hyp := 1592, conc := 1590, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1592, conc := 1591, proof := sorry })
                      (RArray.leaf { hyp := 1593, conc := 1453, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1593, conc := 1477, proof := sorry })
                      (RArray.leaf { hyp := 1593, conc := 1527, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1595, conc := 1528, proof := sorry })
                      (RArray.leaf { hyp := 1596, conc := 1594, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1596, conc := 1595, proof := sorry })
                      (RArray.leaf { hyp := 1597, conc := 1530, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1598, conc := 1590, proof := sorry })
                      (RArray.leaf { hyp := 158, conc := 150, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1600, conc := 1590, proof := sorry })
                      (RArray.leaf { hyp := 1601, conc := 1588, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1601, conc := 1592, proof := sorry })
                      (RArray.leaf { hyp := 1601, conc := 1596, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1601, conc := 1598, proof := sorry })
                      (RArray.leaf { hyp := 1601, conc := 1599, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1601, conc := 1600, proof := sorry })
                      (RArray.leaf { hyp := 1602, conc := 1497, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1602, conc := 1568, proof := sorry })
                      (RArray.leaf { hyp := 1602, conc := 1585, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1603, conc := 1552, proof := sorry })
                      (RArray.leaf { hyp := 1604, conc := 1535, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1605, conc := 1499, proof := sorry })
                      (RArray.leaf { hyp := 1605, conc := 1536, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1605, conc := 1569, proof := sorry })
                      (RArray.leaf { hyp := 1605, conc := 1587, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1606, conc := 1571, proof := sorry })
                      (RArray.leaf { hyp := 1606, conc := 1603, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1606, conc := 1604, proof := sorry })
                      (RArray.leaf { hyp := 1607, conc := 1501, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1608, conc := 1573, proof := sorry })
                      (RArray.leaf { hyp := 159, conc := 150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1610, conc := 1573, proof := sorry })
                      (RArray.leaf { hyp := 1611, conc := 1504, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1611, conc := 1608, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1611, conc := 1609, proof := sorry })
                      (RArray.leaf { hyp := 1611, conc := 1610, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1612, conc := 1497, proof := sorry })
                      (RArray.leaf { hyp := 1616, conc := 1613, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1616, conc := 1614, proof := sorry })
                      (RArray.leaf { hyp := 1616, conc := 1615, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1617, conc := 1572, proof := sorry })
                      (RArray.leaf { hyp := 1618, conc := 1573, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1620, conc := 1595, proof := sorry })
                      (RArray.leaf { hyp := 1621, conc := 1508, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1621, conc := 1618, proof := sorry })
                      (RArray.leaf { hyp := 1621, conc := 1619, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1621, conc := 1620, proof := sorry })
                      (RArray.leaf { hyp := 1622, conc := 1509, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1622, conc := 1546, proof := sorry })
                      (RArray.leaf { hyp := 1622, conc := 1580, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1623, conc := 1510, proof := sorry })
                      (RArray.leaf { hyp := 1623, conc := 1603, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1625, conc := 1511, proof := sorry })
                      (RArray.leaf { hyp := 1626, conc := 1512, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1626, conc := 1620, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1550, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1567, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1601, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1606, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1611, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1616, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1621, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1623, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1624, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1627, conc := 1625, proof := sorry })
                      (RArray.leaf { hyp := 1627, conc := 1626, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 161, conc := 158, proof := sorry })
                      (RArray.leaf { hyp := 1630, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1631, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1632, conc := 1629, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1632, conc := 1630, proof := sorry })
                      (RArray.leaf { hyp := 1632, conc := 1631, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1633, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1634, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1635, conc := 1633, proof := sorry })
                      (RArray.leaf { hyp := 1636, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1637, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1639, conc := 1630, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1639, conc := 1633, proof := sorry })
                      (RArray.leaf { hyp := 1639, conc := 1636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1640, conc := 1630, proof := sorry })
                      (RArray.leaf { hyp := 1640, conc := 1634, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1640, conc := 1637, proof := sorry })
                      (RArray.leaf { hyp := 1642, conc := 1638, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1643, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1644, conc := 1628, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1646, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1647, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 163, conc := 153, proof := sorry })
                      (RArray.leaf { hyp := 1649, conc := 1630, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1649, conc := 1643, proof := sorry })
                      (RArray.leaf { hyp := 1649, conc := 1646, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1651, conc := 1647, proof := sorry })
                      (RArray.leaf { hyp := 1652, conc := 1648, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1652, conc := 1651, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1653, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1654, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1656, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1657, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 164, conc := 154, proof := sorry })
                      (RArray.leaf { hyp := 164, conc := 162, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1660, conc := 1630, proof := sorry })
                      (RArray.leaf { hyp := 1661, conc := 1631, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1661, conc := 1653, proof := sorry })
                      (RArray.leaf { hyp := 1661, conc := 1657, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1662, conc := 1655, proof := sorry })
                      (RArray.leaf { hyp := 1663, conc := 1633, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1663, conc := 1643, proof := sorry })
                      (RArray.leaf { hyp := 1663, conc := 1653, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1666, conc := 1664, proof := sorry })
                      (RArray.leaf { hyp := 1666, conc := 1665, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1667, conc := 1633, proof := sorry })
                      (RArray.leaf { hyp := 1667, conc := 1646, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1667, conc := 1656, proof := sorry })
                      (RArray.leaf { hyp := 165, conc := 150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1669, conc := 1634, proof := sorry })
                      (RArray.leaf { hyp := 1669, conc := 1646, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1670, conc := 1635, proof := sorry })
                      (RArray.leaf { hyp := 1670, conc := 1648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1671, conc := 1636, proof := sorry })
                      (RArray.leaf { hyp := 1671, conc := 1643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1671, conc := 1656, proof := sorry })
                      (RArray.leaf { hyp := 1672, conc := 1636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1672, conc := 1644, proof := sorry })
                      (RArray.leaf { hyp := 1672, conc := 1657, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1674, conc := 1673, proof := sorry })
                      (RArray.leaf { hyp := 1675, conc := 1639, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1675, conc := 1649, proof := sorry })
                      (RArray.leaf { hyp := 1675, conc := 1663, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1675, conc := 1671, proof := sorry })
                      (RArray.leaf { hyp := 1676, conc := 1650, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1676, conc := 1664, proof := sorry })
                      (RArray.leaf { hyp := 1677, conc := 1640, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1677, conc := 1673, proof := sorry })
                      (RArray.leaf { hyp := 1678, conc := 1673, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 166, conc := 150, proof := sorry })
                      (RArray.leaf { hyp := 1679, conc := 1652, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1679, conc := 1666, proof := sorry })
                      (RArray.leaf { hyp := 1679, conc := 1670, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1679, conc := 1674, proof := sorry })
                      (RArray.leaf { hyp := 1679, conc := 1677, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1679, conc := 1678, proof := sorry })
                      (RArray.leaf { hyp := 1680, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1681, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1683, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1684, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 1630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1686, conc := 1680, proof := sorry })
                      (RArray.leaf { hyp := 1686, conc := 1683, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 167, conc := 166, proof := sorry })
                      (RArray.leaf { hyp := 1689, conc := 1682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1689, conc := 1685, proof := sorry })
                      (RArray.leaf { hyp := 1690, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1691, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1693, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 15, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 1699, conc := 1695, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1700, conc := 1633, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1700, conc := 1680, proof := sorry })
                      (RArray.leaf { hyp := 1700, conc := 1690, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1702, conc := 1691, proof := sorry })
                      (RArray.leaf { hyp := 1703, conc := 1682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1703, conc := 1702, proof := sorry })
                      (RArray.leaf { hyp := 1704, conc := 1633, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1704, conc := 1683, proof := sorry })
                      (RArray.leaf { hyp := 1704, conc := 1693, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1706, conc := 1634, proof := sorry })
                      (RArray.leaf { hyp := 1706, conc := 1683, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1706, conc := 1694, proof := sorry })
                      (RArray.leaf { hyp := 1707, conc := 1695, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1709, conc := 1681, proof := sorry })
                      (RArray.leaf { hyp := 1711, conc := 1695, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1711, conc := 1710, proof := sorry })
                      (RArray.leaf { hyp := 1712, conc := 1708, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1713, conc := 1687, proof := sorry })
                      (RArray.leaf { hyp := 1713, conc := 1697, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1713, conc := 1701, proof := sorry })
                      (RArray.leaf { hyp := 1714, conc := 1686, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1714, conc := 1702, proof := sorry })
                      (RArray.leaf { hyp := 1714, conc := 1710, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1715, conc := 1705, proof := sorry })
                      (RArray.leaf { hyp := 1716, conc := 1714, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1716, conc := 1715, proof := sorry })
                      (RArray.leaf { hyp := 1718, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 170, conc := 151, proof := sorry })
                      (RArray.leaf { hyp := 1720, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1721, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1723, conc := 1630, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1723, conc := 1717, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1723, conc := 1720, proof := sorry })
                      (RArray.leaf { hyp := 1726, conc := 1719, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1726, conc := 1722, proof := sorry })
                      (RArray.leaf { hyp := 1726, conc := 1724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1727, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 1728, conc := 1628, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 171, conc := 168, proof := sorry })
                      (RArray.leaf { hyp := 1730, conc := 1628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1734, conc := 1731, proof := sorry })
                      (RArray.leaf { hyp := 1736, conc := 1729, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1736, conc := 1735, proof := sorry })
                      (RArray.leaf { hyp := 1737, conc := 1633, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1737, conc := 1717, proof := sorry })
                      (RArray.leaf { hyp := 1737, conc := 1727, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1740, conc := 1729, proof := sorry })
                      (RArray.leaf { hyp := 1744, conc := 1743, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1745, conc := 1636, proof := sorry })
                      (RArray.leaf { hyp := 1745, conc := 1717, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1745, conc := 1730, proof := sorry })
                      (RArray.leaf { hyp := 1746, conc := 1718, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1748, conc := 1747, proof := sorry })
                      (RArray.leaf { hyp := 1749, conc := 1733, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1750, conc := 1734, proof := sorry })
                      (RArray.leaf { hyp := 1750, conc := 1738, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1750, conc := 1742, proof := sorry })
                      (RArray.leaf { hyp := 1750, conc := 1746, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1753, conc := 1740, proof := sorry })
                      (RArray.leaf { hyp := 1753, conc := 1751, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1753, conc := 1752, proof := sorry })
                      (RArray.leaf { hyp := 1757, conc := 1682, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1757, conc := 1719, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1761, conc := 1759, proof := sorry })
                      (RArray.leaf { hyp := 1762, conc := 1720, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1763, conc := 1681, proof := sorry })
                      (RArray.leaf { hyp := 1765, conc := 1682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1766, conc := 1723, proof := sorry })
                      (RArray.leaf { hyp := 1766, conc := 1758, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1767, conc := 1755, proof := sorry })
                      (RArray.leaf { hyp := 1767, conc := 1759, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1768, conc := 1756, proof := sorry })
                      (RArray.leaf { hyp := 1769, conc := 1688, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1769, conc := 1759, proof := sorry })
                      (RArray.leaf { hyp := 1770, conc := 1689, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1770, conc := 1726, proof := sorry })
                      (RArray.leaf { hyp := 1770, conc := 1757, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1770, conc := 1761, proof := sorry })
                      (RArray.leaf { hyp := 1770, conc := 1765, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1770, conc := 1767, proof := sorry })
                      (RArray.leaf { hyp := 1770, conc := 1768, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1774, conc := 1692, proof := sorry })
                      (RArray.leaf { hyp := 1778, conc := 1695, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1778, conc := 1777, proof := sorry })
                      (RArray.leaf { hyp := 176, conc := 150, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1779, conc := 1646, proof := sorry })
                      (RArray.leaf { hyp := 1779, conc := 1690, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1779, conc := 1730, proof := sorry })
                      (RArray.leaf { hyp := 1782, conc := 1692, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1782, conc := 1781, proof := sorry })
                      (RArray.leaf { hyp := 1783, conc := 1696, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1783, conc := 1775, proof := sorry })
                      (RArray.leaf { hyp := 1784, conc := 1772, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1784, conc := 1776, proof := sorry })
                      (RArray.leaf { hyp := 1784, conc := 1780, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1785, conc := 1781, proof := sorry })
                      (RArray.leaf { hyp := 1786, conc := 1781, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1787, conc := 1699, proof := sorry })
                      (RArray.leaf { hyp := 1787, conc := 1774, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1787, conc := 1785, proof := sorry })
                      (RArray.leaf { hyp := 1787, conc := 1786, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1789, conc := 1681, proof := sorry })
                      (RArray.leaf { hyp := 1789, conc := 1728, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1791, conc := 1682, proof := sorry })
                      (RArray.leaf { hyp := 1791, conc := 1790, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1792, conc := 1653, proof := sorry })
                      (RArray.leaf { hyp := 1792, conc := 1683, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1792, conc := 1730, proof := sorry })
                      (RArray.leaf { hyp := 1795, conc := 1794, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 178, conc := 150, proof := sorry })
                      (RArray.leaf { hyp := 1799, conc := 1682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1799, conc := 1798, proof := sorry })
                      (RArray.leaf { hyp := 1800, conc := 1788, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1801, conc := 1793, proof := sorry })
                      (RArray.leaf { hyp := 1801, conc := 1797, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1804, conc := 1791, proof := sorry })
                      (RArray.leaf { hyp := 1804, conc := 1802, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1804, conc := 1803, proof := sorry })
                      (RArray.leaf { hyp := 1805, conc := 1737, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1805, conc := 1771, proof := sorry })
                      (RArray.leaf { hyp := 1806, conc := 1701, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1806, conc := 1738, proof := sorry })
                      (RArray.leaf { hyp := 1806, conc := 1755, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1806, conc := 1772, proof := sorry })
                      (RArray.leaf { hyp := 1806, conc := 1789, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1807, conc := 1756, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1808, conc := 1772, proof := sorry })
                      (RArray.leaf { hyp := 1809, conc := 1757, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1809, conc := 1791, proof := sorry })
                      (RArray.leaf { hyp := 1809, conc := 1807, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1810, conc := 1775, proof := sorry })
                      (RArray.leaf { hyp := 1811, conc := 1759, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1814, conc := 1707, proof := sorry })
                      (RArray.leaf { hyp := 1814, conc := 1811, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1814, conc := 1812, proof := sorry })
                      (RArray.leaf { hyp := 1814, conc := 1813, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1815, conc := 1700, proof := sorry })
                      (RArray.leaf { hyp := 1815, conc := 1741, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1815, conc := 1796, proof := sorry })
                      (RArray.leaf { hyp := 180, conc := 179, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1819, conc := 1703, proof := sorry })
                      (RArray.leaf { hyp := 1819, conc := 1816, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1819, conc := 1817, proof := sorry })
                      (RArray.leaf { hyp := 1819, conc := 1818, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1820, conc := 1708, proof := sorry })
                      (RArray.leaf { hyp := 1820, conc := 1775, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1822, conc := 1756, proof := sorry })
                      (RArray.leaf { hyp := 1824, conc := 1711, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1824, conc := 1757, proof := sorry })
                      (RArray.leaf { hyp := 1824, conc := 1822, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1824, conc := 1823, proof := sorry })
                      (RArray.leaf { hyp := 1825, conc := 1712, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1825, conc := 1783, proof := sorry })
                      (RArray.leaf { hyp := 1825, conc := 1810, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1828, conc := 1714, proof := sorry })
                      (RArray.leaf { hyp := 1830, conc := 1716, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1830, conc := 1829, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1832, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1833, conc := 1831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1834, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1836, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1837, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1838, conc := 1832, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1838, conc := 1836, proof := sorry })
                      (RArray.leaf { hyp := 1838, conc := 1837, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1839, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1840, conc := 1831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1842, conc := 1833, proof := sorry })
                      (RArray.leaf { hyp := 1842, conc := 1836, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1842, conc := 1839, proof := sorry })
                      (RArray.leaf { hyp := 1844, conc := 1834, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1844, conc := 1836, proof := sorry })
                      (RArray.leaf { hyp := 1844, conc := 1840, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1845, conc := 1841, proof := sorry })
                      (RArray.leaf { hyp := 1845, conc := 1844, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1846, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1847, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 1832, proof := sorry })
                      (RArray.leaf { hyp := 1848, conc := 1846, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1848, conc := 1847, proof := sorry })
                      (RArray.leaf { hyp := 1849, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1850, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1852, conc := 1833, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1852, conc := 1846, proof := sorry })
                      (RArray.leaf { hyp := 1852, conc := 1849, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1854, conc := 1834, proof := sorry })
                      (RArray.leaf { hyp := 1854, conc := 1846, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1854, conc := 1850, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1855, conc := 1835, proof := sorry })
                      (RArray.leaf { hyp := 1855, conc := 1853, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1855, conc := 1854, proof := sorry })
                      (RArray.leaf { hyp := 1856, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1857, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1858, conc := 1832, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 184, conc := 177, proof := sorry })
                      (RArray.leaf { hyp := 184, conc := 182, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 184, conc := 183, proof := sorry })
                      (RArray.leaf { hyp := 1859, conc := 1831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1860, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1862, conc := 1833, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1862, conc := 1856, proof := sorry })
                      (RArray.leaf { hyp := 1862, conc := 1859, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1864, conc := 1834, proof := sorry })
                      (RArray.leaf { hyp := 1864, conc := 1856, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1864, conc := 1860, proof := sorry })
                      (RArray.leaf { hyp := 1865, conc := 1863, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1866, conc := 1836, proof := sorry })
                      (RArray.leaf { hyp := 1866, conc := 1846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1866, conc := 1856, proof := sorry })
                      (RArray.leaf { hyp := 1867, conc := 1836, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1867, conc := 1847, proof := sorry })
                      (RArray.leaf { hyp := 1867, conc := 1857, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 185, conc := 175, proof := sorry })
                      (RArray.leaf { hyp := 1870, conc := 1836, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1870, conc := 1849, proof := sorry })
                      (RArray.leaf { hyp := 1870, conc := 1859, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1871, conc := 1850, proof := sorry })
                      (RArray.leaf { hyp := 1872, conc := 1837, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1872, conc := 1849, proof := sorry })
                      (RArray.leaf { hyp := 1872, conc := 1860, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1873, conc := 1838, proof := sorry })
                      (RArray.leaf { hyp := 1873, conc := 1851, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1873, conc := 1861, proof := sorry })
                      (RArray.leaf { hyp := 1873, conc := 1870, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1873, conc := 1871, proof := sorry })
                      (RArray.leaf { hyp := 1874, conc := 1839, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1874, conc := 1846, proof := sorry })
                      (RArray.leaf { hyp := 1874, conc := 1859, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1875, conc := 1839, proof := sorry })
                      (RArray.leaf { hyp := 1875, conc := 1847, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1875, conc := 1860, proof := sorry })
                      (RArray.leaf { hyp := 1877, conc := 1841, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1877, conc := 1876, proof := sorry })
                      (RArray.leaf { hyp := 1878, conc := 1842, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1878, conc := 1852, proof := sorry })
                      (RArray.leaf { hyp := 1878, conc := 1862, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1878, conc := 1866, proof := sorry })
                      (RArray.leaf { hyp := 1878, conc := 1870, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1878, conc := 1874, proof := sorry })
                      (RArray.leaf { hyp := 1879, conc := 1863, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1880, conc := 1863, proof := sorry })
                      (RArray.leaf { hyp := 1882, conc := 1845, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1882, conc := 1865, proof := sorry })
                      (RArray.leaf { hyp := 1882, conc := 1878, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1882, conc := 1879, proof := sorry })
                      (RArray.leaf { hyp := 1882, conc := 1880, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1884, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1886, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1887, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1892, conc := 1885, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1892, conc := 1890, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1892, conc := 1891, proof := sorry })
                      (RArray.leaf { hyp := 1893, conc := 1831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1894, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1896, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1897, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 17, conc := 16, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1901, conc := 1893, proof := sorry })
                      (RArray.leaf { hyp := 1901, conc := 1897, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1902, conc := 1895, proof := sorry })
                      (RArray.leaf { hyp := 1902, conc := 1898, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1903, conc := 1836, proof := sorry })
                      (RArray.leaf { hyp := 1906, conc := 1885, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1906, conc := 1905, proof := sorry })
                      (RArray.leaf { hyp := 1910, conc := 1908, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1912, conc := 1884, proof := sorry })
                      (RArray.leaf { hyp := 1912, conc := 1897, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1914, conc := 1885, proof := sorry })
                      (RArray.leaf { hyp := 1914, conc := 1913, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1915, conc := 1907, proof := sorry })
                      (RArray.leaf { hyp := 1916, conc := 1900, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1916, conc := 1904, proof := sorry })
                      (RArray.leaf { hyp := 1916, conc := 1908, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1917, conc := 1913, proof := sorry })
                      (RArray.leaf { hyp := 1918, conc := 1913, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1919, conc := 1892, proof := sorry })
                      (RArray.leaf { hyp := 1919, conc := 1910, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1919, conc := 1914, proof := sorry })
                      (RArray.leaf { hyp := 1919, conc := 1917, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1919, conc := 1918, proof := sorry })
                      (RArray.leaf { hyp := 1920, conc := 1831, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1921, conc := 1831, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1923, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1924, conc := 1831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1930, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 1931, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1933, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 192, conc := 170, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 192, conc := 180, proof := sorry })
                      (RArray.leaf { hyp := 192, conc := 190, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 192, conc := 191, proof := sorry })
                      (RArray.leaf { hyp := 1939, conc := 1935, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1939, conc := 1937, proof := sorry })
                      (RArray.leaf { hyp := 1939, conc := 1938, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1943, conc := 1932, proof := sorry })
                      (RArray.leaf { hyp := 1943, conc := 1941, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1947, conc := 1925, proof := sorry })
                      (RArray.leaf { hyp := 1947, conc := 1945, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1947, conc := 1946, proof := sorry })
                      (RArray.leaf { hyp := 1948, conc := 1839, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1948, conc := 1920, proof := sorry })
                      (RArray.leaf { hyp := 193, conc := 165, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 193, conc := 178, proof := sorry })
                      (RArray.leaf { hyp := 1951, conc := 1949, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1951, conc := 1950, proof := sorry })
                      (RArray.leaf { hyp := 1952, conc := 1936, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1953, conc := 1949, proof := sorry })
                      (RArray.leaf { hyp := 1956, conc := 1929, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1956, conc := 1939, proof := sorry })
                      (RArray.leaf { hyp := 1956, conc := 1947, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1956, conc := 1951, proof := sorry })
                      (RArray.leaf { hyp := 1956, conc := 1953, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1956, conc := 1954, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1956, conc := 1955, proof := sorry })
                      (RArray.leaf { hyp := 1957, conc := 1846, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1957, conc := 1883, proof := sorry })
                      (RArray.leaf { hyp := 1957, conc := 1920, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1960, conc := 1885, proof := sorry })
                      (RArray.leaf { hyp := 1960, conc := 1959, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1964, conc := 1925, proof := sorry })
                      (RArray.leaf { hyp := 1964, conc := 1962, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1965, conc := 1923, proof := sorry })
                      (RArray.leaf { hyp := 1966, conc := 1884, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1968, conc := 1885, proof := sorry })
                      (RArray.leaf { hyp := 1968, conc := 1967, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1969, conc := 1965, proof := sorry })
                      (RArray.leaf { hyp := 1970, conc := 1958, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1971, conc := 1927, proof := sorry })
                      (RArray.leaf { hyp := 1971, conc := 1959, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1972, conc := 1854, proof := sorry })
                      (RArray.leaf { hyp := 1972, conc := 1962, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1973, conc := 1964, proof := sorry })
                      (RArray.leaf { hyp := 1973, conc := 1968, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1973, conc := 1970, proof := sorry })
                      (RArray.leaf { hyp := 1973, conc := 1971, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1973, conc := 1972, proof := sorry })
                      (RArray.leaf { hyp := 1974, conc := 1846, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1974, conc := 1893, proof := sorry })
                      (RArray.leaf { hyp := 1974, conc := 1930, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1976, conc := 1847, proof := sorry })
                      (RArray.leaf { hyp := 1976, conc := 1893, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1977, conc := 1848, proof := sorry })
                      (RArray.leaf { hyp := 1977, conc := 1932, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1978, conc := 1846, proof := sorry })
                      (RArray.leaf { hyp := 1978, conc := 1896, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 196, conc := 195, proof := sorry })
                      (RArray.leaf { hyp := 1981, conc := 1980, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1982, conc := 1849, proof := sorry })
                      (RArray.leaf { hyp := 1982, conc := 1893, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1982, conc := 1933, proof := sorry })
                      (RArray.leaf { hyp := 1983, conc := 1894, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1984, conc := 1893, proof := sorry })
                      (RArray.leaf { hyp := 1985, conc := 1983, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1986, conc := 1936, proof := sorry })
                      (RArray.leaf { hyp := 1986, conc := 1974, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1987, conc := 1975, proof := sorry })
                      (RArray.leaf { hyp := 197, conc := 171, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 197, conc := 189, proof := sorry })
                      (RArray.leaf { hyp := 1990, conc := 1989, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1992, conc := 1884, proof := sorry })
                      (RArray.leaf { hyp := 1992, conc := 1931, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1994, conc := 1858, proof := sorry })
                      (RArray.leaf { hyp := 1994, conc := 1932, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1994, conc := 1993, proof := sorry })
                      (RArray.leaf { hyp := 1995, conc := 1856, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1995, conc := 1886, proof := sorry })
                      (RArray.leaf { hyp := 1995, conc := 1933, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1996, conc := 1887, proof := sorry })
                      (RArray.leaf { hyp := 1997, conc := 1934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1998, conc := 1888, proof := sorry })
                      (RArray.leaf { hyp := 1998, conc := 1997, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 198, conc := 190, proof := sorry })
                      (RArray.leaf { hyp := 18, conc := 12, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1999, conc := 1859, proof := sorry })
                      (RArray.leaf { hyp := 1999, conc := 1883, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2002, conc := 2000, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2002, conc := 2001, proof := sorry })
                      (RArray.leaf { hyp := 2003, conc := 1936, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2004, conc := 1996, proof := sorry })
                      (RArray.leaf { hyp := 2005, conc := 1997, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2007, conc := 2002, proof := sorry })
                      (RArray.leaf { hyp := 2007, conc := 2004, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2007, conc := 2005, proof := sorry })
                      (RArray.leaf { hyp := 2007, conc := 2006, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2008, conc := 1991, proof := sorry })
                      (RArray.leaf { hyp := 199, conc := 182, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2009, conc := 1904, proof := sorry })
                      (RArray.leaf { hyp := 2009, conc := 1941, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2009, conc := 1958, proof := sorry })
                      (RArray.leaf { hyp := 2010, conc := 1993, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2011, conc := 1975, proof := sorry })
                      (RArray.leaf { hyp := 2012, conc := 1906, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2012, conc := 1943, proof := sorry })
                      (RArray.leaf { hyp := 2012, conc := 1960, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2012, conc := 1977, proof := sorry })
                      (RArray.leaf { hyp := 2012, conc := 2010, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2012, conc := 2011, proof := sorry })
                      (RArray.leaf { hyp := 2013, conc := 1907, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2013, conc := 1961, proof := sorry })
                      (RArray.leaf { hyp := 2015, conc := 1997, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2016, conc := 1997, proof := sorry })
                      (RArray.leaf { hyp := 2017, conc := 2014, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2017, conc := 2015, proof := sorry })
                      (RArray.leaf { hyp := 2017, conc := 2016, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2018, conc := 1903, proof := sorry })
                      (RArray.leaf { hyp := 2018, conc := 1965, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2022, conc := 2019, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2022, conc := 2020, proof := sorry })
                      (RArray.leaf { hyp := 2022, conc := 2021, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2023, conc := 1874, proof := sorry })
                      (RArray.leaf { hyp := 2023, conc := 1911, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2023, conc := 1957, proof := sorry })
                      (RArray.leaf { hyp := 2023, conc := 1978, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2023, conc := 1999, proof := sorry })
                      (RArray.leaf { hyp := 2027, conc := 2024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2027, conc := 2025, proof := sorry })
                      (RArray.leaf { hyp := 2027, conc := 2026, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2028, conc := 1878, proof := sorry })
                      (RArray.leaf { hyp := 2028, conc := 1915, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2028, conc := 1952, proof := sorry })
                      (RArray.leaf { hyp := 2028, conc := 1969, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2028, conc := 1986, proof := sorry })
                      (RArray.leaf { hyp := 2028, conc := 2003, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2028, conc := 2018, proof := sorry })
                      (RArray.leaf { hyp := 201, conc := 192, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2029, conc := 2019, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 1956, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2033, conc := 1973, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 1990, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2033, conc := 2007, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 2017, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2033, conc := 2022, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 2027, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2033, conc := 2029, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 2030, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2033, conc := 2031, proof := sorry })
                      (RArray.leaf { hyp := 2033, conc := 2032, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2035, conc := 2034, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2036, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2037, conc := 2034, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2039, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2040, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2041, conc := 2035, proof := sorry })
                      (RArray.leaf { hyp := 2042, conc := 2034, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2043, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2044, conc := 2035, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2044, conc := 2042, proof := sorry })
                      (RArray.leaf { hyp := 2044, conc := 2043, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2045, conc := 2039, proof := sorry })
                      (RArray.leaf { hyp := 2045, conc := 2042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2048, conc := 2041, proof := sorry })
                      (RArray.leaf { hyp := 2048, conc := 2046, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2048, conc := 2047, proof := sorry })
                      (RArray.leaf { hyp := 2049, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2050, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2051, conc := 2035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2051, conc := 2049, proof := sorry })
                      (RArray.leaf { hyp := 2051, conc := 2050, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2052, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2053, conc := 2034, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2054, conc := 2035, proof := sorry })
                      (RArray.leaf { hyp := 2054, conc := 2052, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2054, conc := 2053, proof := sorry })
                      (RArray.leaf { hyp := 2055, conc := 2036, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2055, conc := 2049, proof := sorry })
                      (RArray.leaf { hyp := 2055, conc := 2052, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2058, conc := 2056, proof := sorry })
                      (RArray.leaf { hyp := 2058, conc := 2057, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2059, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2060, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2061, conc := 2035, proof := sorry })
                      (RArray.leaf { hyp := 2061, conc := 2060, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2062, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2063, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2064, conc := 2035, proof := sorry })
                      (RArray.leaf { hyp := 2064, conc := 2062, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2064, conc := 2063, proof := sorry })
                      (RArray.leaf { hyp := 2065, conc := 2036, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2065, conc := 2059, proof := sorry })
                      (RArray.leaf { hyp := 2065, conc := 2062, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2067, conc := 2037, proof := sorry })
                      (RArray.leaf { hyp := 2068, conc := 2038, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 205, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 2069, conc := 2039, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2069, conc := 2049, proof := sorry })
                      (RArray.leaf { hyp := 2069, conc := 2059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2071, conc := 2040, proof := sorry })
                      (RArray.leaf { hyp := 2072, conc := 2041, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2072, conc := 2070, proof := sorry })
                      (RArray.leaf { hyp := 2072, conc := 2071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2075, conc := 2040, proof := sorry })
                      (RArray.leaf { hyp := 2075, conc := 2052, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2076, conc := 2041, proof := sorry })
                      (RArray.leaf { hyp := 2076, conc := 2054, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2076, conc := 2073, proof := sorry })
                      (RArray.leaf { hyp := 2076, conc := 2074, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2077, conc := 2042, proof := sorry })
                      (RArray.leaf { hyp := 2077, conc := 2049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2077, conc := 2062, proof := sorry })
                      (RArray.leaf { hyp := 2078, conc := 2042, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2078, conc := 2050, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2078, conc := 2063, proof := sorry })
                      (RArray.leaf { hyp := 206, conc := 203, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 206, conc := 205, proof := sorry })
                      (RArray.leaf { hyp := 2080, conc := 2044, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2080, conc := 2051, proof := sorry })
                      (RArray.leaf { hyp := 2080, conc := 2064, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2080, conc := 2079, proof := sorry })
                      (RArray.leaf { hyp := 2081, conc := 2045, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2081, conc := 2065, proof := sorry })
                      (RArray.leaf { hyp := 2081, conc := 2069, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2081, conc := 2073, proof := sorry })
                      (RArray.leaf { hyp := 2081, conc := 2077, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2082, conc := 2070, proof := sorry })
                      (RArray.leaf { hyp := 2083, conc := 2046, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2083, conc := 2075, proof := sorry })
                      (RArray.leaf { hyp := 2084, conc := 2074, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2085, conc := 2048, proof := sorry })
                      (RArray.leaf { hyp := 2085, conc := 2072, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2085, conc := 2076, proof := sorry })
                      (RArray.leaf { hyp := 2085, conc := 2080, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2085, conc := 2082, proof := sorry })
                      (RArray.leaf { hyp := 2085, conc := 2083, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2085, conc := 2084, proof := sorry })
                      (RArray.leaf { hyp := 2086, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2087, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2088, conc := 2035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2088, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2088, conc := 2087, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2089, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2090, conc := 2034, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2092, conc := 2036, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2092, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2092, conc := 2089, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2095, conc := 2091, proof := sorry })
                      (RArray.leaf { hyp := 2095, conc := 2093, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2096, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2097, conc := 2034, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 208, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 19, conc := 16, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2100, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2105, conc := 2101, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2105, conc := 2103, proof := sorry })
                      (RArray.leaf { hyp := 2109, conc := 2107, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2112, conc := 2100, proof := sorry })
                      (RArray.leaf { hyp := 2113, conc := 2091, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2113, conc := 2111, proof := sorry })
                      (RArray.leaf { hyp := 2114, conc := 2042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2114, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2114, conc := 2099, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2115, conc := 2042, proof := sorry })
                      (RArray.leaf { hyp := 2115, conc := 2087, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2117, conc := 2116, proof := sorry })
                      (RArray.leaf { hyp := 2118, conc := 2102, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 210, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 2119, conc := 2093, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2119, conc := 2107, proof := sorry })
                      (RArray.leaf { hyp := 2120, conc := 2116, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2121, conc := 2111, proof := sorry })
                      (RArray.leaf { hyp := 2122, conc := 2095, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2122, conc := 2105, proof := sorry })
                      (RArray.leaf { hyp := 2122, conc := 2113, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2122, conc := 2117, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2122, conc := 2119, proof := sorry })
                      (RArray.leaf { hyp := 2122, conc := 2120, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2122, conc := 2121, proof := sorry })
                      (RArray.leaf { hyp := 2123, conc := 2034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2124, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2125, conc := 2035, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2125, conc := 2123, proof := sorry })
                      (RArray.leaf { hyp := 2125, conc := 2124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2126, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2127, conc := 2034, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 211, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 2131, conc := 2037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2131, conc := 2123, proof := sorry })
                      (RArray.leaf { hyp := 2131, conc := 2127, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2132, conc := 2128, proof := sorry })
                      (RArray.leaf { hyp := 2132, conc := 2130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2133, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2136, conc := 2034, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2138, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2140, conc := 2137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2141, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2142, conc := 2138, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2142, conc := 2140, proof := sorry })
                      (RArray.leaf { hyp := 2142, conc := 2141, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2145, conc := 2040, proof := sorry })
                      (RArray.leaf { hyp := 2146, conc := 2135, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2146, conc := 2144, proof := sorry })
                      (RArray.leaf { hyp := 2148, conc := 2137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2149, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2150, conc := 2148, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2150, conc := 2149, proof := sorry })
                      (RArray.leaf { hyp := 2151, conc := 2042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2151, conc := 2123, proof := sorry })
                      (RArray.leaf { hyp := 2151, conc := 2136, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2152, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2153, conc := 2137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2154, conc := 2152, proof := sorry })
                      (RArray.leaf { hyp := 2154, conc := 2153, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2155, conc := 2129, proof := sorry })
                      (RArray.leaf { hyp := 2157, conc := 2153, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2158, conc := 2153, proof := sorry })
                      (RArray.leaf { hyp := 214, conc := 211, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2159, conc := 2132, proof := sorry })
                      (RArray.leaf { hyp := 2159, conc := 2142, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2159, conc := 2150, proof := sorry })
                      (RArray.leaf { hyp := 2159, conc := 2154, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2159, conc := 2156, proof := sorry })
                      (RArray.leaf { hyp := 2159, conc := 2157, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2159, conc := 2158, proof := sorry })
                      (RArray.leaf { hyp := 2160, conc := 2049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2160, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2160, conc := 2123, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2161, conc := 2049, proof := sorry })
                      (RArray.leaf { hyp := 2161, conc := 2087, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2161, conc := 2124, proof := sorry })
                      (RArray.leaf { hyp := 2162, conc := 2050, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2162, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2162, conc := 2124, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2163, conc := 2051, proof := sorry })
                      (RArray.leaf { hyp := 2163, conc := 2088, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2163, conc := 2125, proof := sorry })
                      (RArray.leaf { hyp := 2163, conc := 2160, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2163, conc := 2161, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2163, conc := 2162, proof := sorry })
                      (RArray.leaf { hyp := 2166, conc := 2089, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2167, conc := 2165, proof := sorry })
                      (RArray.leaf { hyp := 2171, conc := 2128, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2172, conc := 2129, proof := sorry })
                      (RArray.leaf { hyp := 2173, conc := 2165, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2174, conc := 2130, proof := sorry })
                      (RArray.leaf { hyp := 2175, conc := 2094, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2175, conc := 2165, proof := sorry })
                      (RArray.leaf { hyp := 2175, conc := 2170, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2176, conc := 2167, proof := sorry })
                      (RArray.leaf { hyp := 2176, conc := 2173, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 216, conc := 206, proof := sorry })
                      (RArray.leaf { hyp := 216, conc := 209, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 216, conc := 212, proof := sorry })
                      (RArray.leaf { hyp := 2179, conc := 2050, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2179, conc := 2096, proof := sorry })
                      (RArray.leaf { hyp := 2180, conc := 2098, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2182, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2183, conc := 2137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2184, conc := 2182, proof := sorry })
                      (RArray.leaf { hyp := 2184, conc := 2183, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2185, conc := 2052, proof := sorry })
                      (RArray.leaf { hyp := 2185, conc := 2096, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2186, conc := 2097, proof := sorry })
                      (RArray.leaf { hyp := 2186, conc := 2137, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2187, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2188, conc := 2186, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2188, conc := 2187, proof := sorry })
                      (RArray.leaf { hyp := 2189, conc := 2102, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2189, conc := 2181, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2189, conc := 2185, proof := sorry })
                      (RArray.leaf { hyp := 2191, conc := 2187, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2192, conc := 2187, proof := sorry })
                      (RArray.leaf { hyp := 2193, conc := 2184, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2193, conc := 2188, proof := sorry })
                      (RArray.leaf { hyp := 2193, conc := 2190, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2193, conc := 2191, proof := sorry })
                      (RArray.leaf { hyp := 2193, conc := 2192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2195, conc := 2087, proof := sorry })
                      (RArray.leaf { hyp := 2197, conc := 2135, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2198, conc := 2059, proof := sorry })
                      (RArray.leaf { hyp := 2198, conc := 2089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 218, conc := 202, proof := sorry })
                      (RArray.leaf { hyp := 2199, conc := 2090, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2200, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2201, conc := 2199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2201, conc := 2200, proof := sorry })
                      (RArray.leaf { hyp := 2202, conc := 2062, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2202, conc := 2086, proof := sorry })
                      (RArray.leaf { hyp := 2202, conc := 2136, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2203, conc := 2137, proof := sorry })
                      (RArray.leaf { hyp := 2204, conc := 2137, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2205, conc := 2203, proof := sorry })
                      (RArray.leaf { hyp := 2205, conc := 2204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2206, conc := 2092, proof := sorry })
                      (RArray.leaf { hyp := 2206, conc := 2139, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2206, conc := 2194, proof := sorry })
                      (RArray.leaf { hyp := 2208, conc := 2204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2209, conc := 2204, proof := sorry })
                      (RArray.leaf { hyp := 2210, conc := 2201, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2210, conc := 2205, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2210, conc := 2207, proof := sorry })
                      (RArray.leaf { hyp := 2210, conc := 2208, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2210, conc := 2209, proof := sorry })
                      (RArray.leaf { hyp := 2211, conc := 2106, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2211, conc := 2143, proof := sorry })
                      (RArray.leaf { hyp := 2212, conc := 2107, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2213, conc := 2144, proof := sorry })
                      (RArray.leaf { hyp := 2214, conc := 2071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2214, conc := 2145, proof := sorry })
                      (RArray.leaf { hyp := 2214, conc := 2178, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2214, conc := 2196, proof := sorry })
                      (RArray.leaf { hyp := 2215, conc := 2072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2215, conc := 2146, proof := sorry })
                      (RArray.leaf { hyp := 2215, conc := 2180, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2215, conc := 2197, proof := sorry })
                      (RArray.leaf { hyp := 2215, conc := 2212, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2215, conc := 2213, proof := sorry })
                      (RArray.leaf { hyp := 2215, conc := 2214, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2216, conc := 2110, proof := sorry })
                      (RArray.leaf { hyp := 2217, conc := 2199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2218, conc := 2200, proof := sorry })
                      (RArray.leaf { hyp := 220, conc := 202, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2219, conc := 2200, proof := sorry })
                      (RArray.leaf { hyp := 2220, conc := 2217, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2220, conc := 2218, proof := sorry })
                      (RArray.leaf { hyp := 2220, conc := 2219, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2222, conc := 2203, proof := sorry })
                      (RArray.leaf { hyp := 2223, conc := 2204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2224, conc := 2204, proof := sorry })
                      (RArray.leaf { hyp := 2225, conc := 2222, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2225, conc := 2223, proof := sorry })
                      (RArray.leaf { hyp := 2225, conc := 2224, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2226, conc := 2077, proof := sorry })
                      (RArray.leaf { hyp := 2226, conc := 2114, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2226, conc := 2151, proof := sorry })
                      (RArray.leaf { hyp := 2226, conc := 2181, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2226, conc := 2202, proof := sorry })
                      (RArray.leaf { hyp := 2228, conc := 2204, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2229, conc := 2204, proof := sorry })
                      (RArray.leaf { hyp := 2230, conc := 2163, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2230, conc := 2227, proof := sorry })
                      (RArray.leaf { hyp := 2230, conc := 2228, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2230, conc := 2229, proof := sorry })
                      (RArray.leaf { hyp := 2231, conc := 2081, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2231, conc := 2118, proof := sorry })
                      (RArray.leaf { hyp := 2231, conc := 2189, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2234, conc := 2229, proof := sorry })
                      (RArray.leaf { hyp := 2235, conc := 2217, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2159, proof := sorry })
                      (RArray.leaf { hyp := 2236, conc := 2176, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2193, proof := sorry })
                      (RArray.leaf { hyp := 2236, conc := 2210, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2220, proof := sorry })
                      (RArray.leaf { hyp := 2236, conc := 2225, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2230, proof := sorry })
                      (RArray.leaf { hyp := 2236, conc := 2232, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2233, proof := sorry })
                      (RArray.leaf { hyp := 2236, conc := 2234, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2236, conc := 2235, proof := sorry })
                      (RArray.leaf { hyp := 2239, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2240, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2241, conc := 2238, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2242, conc := 2237, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2243, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2244, conc := 2238, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2245, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2246, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2247, conc := 2238, proof := sorry })
                      (RArray.leaf { hyp := 2248, conc := 2239, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2248, conc := 2242, proof := sorry })
                      (RArray.leaf { hyp := 2248, conc := 2245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2250, conc := 2246, proof := sorry })
                      (RArray.leaf { hyp := 2251, conc := 2241, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2251, conc := 2244, proof := sorry })
                      (RArray.leaf { hyp := 2251, conc := 2247, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2251, conc := 2250, proof := sorry })
                      (RArray.leaf { hyp := 2252, conc := 2237, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2253, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2254, conc := 2238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2255, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2256, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2257, conc := 2238, proof := sorry })
                      (RArray.leaf { hyp := 2258, conc := 2252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2258, conc := 2255, proof := sorry })
                      (RArray.leaf { hyp := 2259, conc := 2239, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2259, conc := 2253, proof := sorry })
                      (RArray.leaf { hyp := 2259, conc := 2256, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2260, conc := 2240, proof := sorry })
                      (RArray.leaf { hyp := 2261, conc := 2254, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2261, conc := 2257, proof := sorry })
                      (RArray.leaf { hyp := 2262, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2263, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2264, conc := 2238, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2265, conc := 2237, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2266, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2267, conc := 2238, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2269, conc := 2239, proof := sorry })
                      (RArray.leaf { hyp := 2269, conc := 2263, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2269, conc := 2266, proof := sorry })
                      (RArray.leaf { hyp := 2270, conc := 2240, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2270, conc := 2262, proof := sorry })
                      (RArray.leaf { hyp := 2270, conc := 2266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2271, conc := 2264, proof := sorry })
                      (RArray.leaf { hyp := 2271, conc := 2267, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2272, conc := 2242, proof := sorry })
                      (RArray.leaf { hyp := 2272, conc := 2252, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2272, conc := 2262, proof := sorry })
                      (RArray.leaf { hyp := 2275, conc := 2264, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2276, conc := 2242, proof := sorry })
                      (RArray.leaf { hyp := 2276, conc := 2255, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2276, conc := 2265, proof := sorry })
                      (RArray.leaf { hyp := 2278, conc := 2243, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2278, conc := 2255, proof := sorry })
                      (RArray.leaf { hyp := 226, conc := 224, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2279, conc := 2267, proof := sorry })
                      (RArray.leaf { hyp := 2280, conc := 2245, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2280, conc := 2252, proof := sorry })
                      (RArray.leaf { hyp := 2280, conc := 2265, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2281, conc := 2245, proof := sorry })
                      (RArray.leaf { hyp := 2281, conc := 2253, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2283, conc := 2267, proof := sorry })
                      (RArray.leaf { hyp := 2284, conc := 2258, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2284, conc := 2268, proof := sorry })
                      (RArray.leaf { hyp := 2284, conc := 2272, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2284, conc := 2276, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2284, conc := 2280, proof := sorry })
                      (RArray.leaf { hyp := 2285, conc := 2248, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2285, conc := 2259, proof := sorry })
                      (RArray.leaf { hyp := 2285, conc := 2269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2285, conc := 2273, proof := sorry })
                      (RArray.leaf { hyp := 2285, conc := 2281, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2286, conc := 2249, proof := sorry })
                      (RArray.leaf { hyp := 2286, conc := 2274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2286, conc := 2282, proof := sorry })
                      (RArray.leaf { hyp := 2287, conc := 2250, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2288, conc := 2261, proof := sorry })
                      (RArray.leaf { hyp := 2288, conc := 2271, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2288, conc := 2275, proof := sorry })
                      (RArray.leaf { hyp := 2288, conc := 2279, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2288, conc := 2283, proof := sorry })
                      (RArray.leaf { hyp := 2288, conc := 2287, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2289, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2290, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2292, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2293, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2295, conc := 2289, proof := sorry })
                      (RArray.leaf { hyp := 2295, conc := 2292, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2298, conc := 2291, proof := sorry })
                      (RArray.leaf { hyp := 2298, conc := 2294, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2298, conc := 2297, proof := sorry })
                      (RArray.leaf { hyp := 228, conc := 202, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 21, conc := 19, proof := sorry })
                      (RArray.leaf { hyp := 2299, conc := 2237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2300, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2302, conc := 2237, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2303, conc := 2237, proof := sorry })
                      (RArray.leaf { hyp := 2308, conc := 2301, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2309, conc := 2242, proof := sorry })
                      (RArray.leaf { hyp := 2309, conc := 2289, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2309, conc := 2299, proof := sorry })
                      (RArray.leaf { hyp := 2312, conc := 2291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2313, conc := 2242, proof := sorry })
                      (RArray.leaf { hyp := 2313, conc := 2292, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2313, conc := 2302, proof := sorry })
                      (RArray.leaf { hyp := 2315, conc := 2243, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2315, conc := 2292, proof := sorry })
                      (RArray.leaf { hyp := 2315, conc := 2303, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2316, conc := 2304, proof := sorry })
                      (RArray.leaf { hyp := 2317, conc := 2245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2317, conc := 2289, proof := sorry })
                      (RArray.leaf { hyp := 2317, conc := 2302, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2318, conc := 2303, proof := sorry })
                      (RArray.leaf { hyp := 230, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2320, conc := 2291, proof := sorry })
                      (RArray.leaf { hyp := 2321, conc := 2309, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2321, conc := 2313, proof := sorry })
                      (RArray.leaf { hyp := 2321, conc := 2317, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2322, conc := 2296, proof := sorry })
                      (RArray.leaf { hyp := 2322, conc := 2310, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2322, conc := 2314, proof := sorry })
                      (RArray.leaf { hyp := 2323, conc := 2311, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2323, conc := 2319, proof := sorry })
                      (RArray.leaf { hyp := 2324, conc := 2314, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2325, conc := 2298, proof := sorry })
                      (RArray.leaf { hyp := 2325, conc := 2308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2325, conc := 2312, proof := sorry })
                      (RArray.leaf { hyp := 2325, conc := 2316, proof := sorry })))))))))))

end EndToEnd
