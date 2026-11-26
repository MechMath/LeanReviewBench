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
def _root_.EndToEnd.dualtable0 : RArray EndToEnd.DualFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 0, dual := 0, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1, dual := 1, proof := sorry })
                      (RArray.leaf { law := 2, dual := 2, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3, dual := 4, proof := sorry })
                      (RArray.leaf { law := 4, dual := 3, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 5, dual := 5, proof := sorry })
                      (RArray.leaf { law := 6, dual := 6, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 7, dual := 22, proof := sorry })
                      (RArray.leaf { law := 8, dual := 27, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 9, dual := 24, proof := sorry })
                      (RArray.leaf { law := 10, dual := 30, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 11, dual := 33, proof := sorry })
                      (RArray.leaf { law := 12, dual := 23, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 13, dual := 28, proof := sorry })
                      (RArray.leaf { law := 14, dual := 29, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 15, dual := 25, proof := sorry })
                      (RArray.leaf { law := 16, dual := 31, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 17, dual := 35, proof := sorry })
                      (RArray.leaf { law := 18, dual := 26, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 19, dual := 34, proof := sorry })
                      (RArray.leaf { law := 20, dual := 32, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 21, dual := 36, proof := sorry })
                      (RArray.leaf { law := 22, dual := 7, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 23, dual := 12, proof := sorry })
                      (RArray.leaf { law := 24, dual := 9, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 25, dual := 15, proof := sorry })
                      (RArray.leaf { law := 26, dual := 18, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 27, dual := 8, proof := sorry })
                      (RArray.leaf { law := 28, dual := 13, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 29, dual := 14, proof := sorry })
                      (RArray.leaf { law := 30, dual := 10, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 31, dual := 16, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 32, dual := 20, proof := sorry })
                      (RArray.leaf { law := 33, dual := 11, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 34, dual := 19, proof := sorry })
                      (RArray.leaf { law := 35, dual := 17, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 36, dual := 21, proof := sorry })
                      (RArray.leaf { law := 37, dual := 38, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 38, dual := 37, proof := sorry })
                      (RArray.leaf { law := 39, dual := 39, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 40, dual := 40, proof := sorry })
                      (RArray.leaf { law := 41, dual := 44, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 42, dual := 42, proof := sorry })
                      (RArray.leaf { law := 43, dual := 43, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 44, dual := 41, proof := sorry })
                      (RArray.leaf { law := 45, dual := 45, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 46, dual := 254, proof := sorry })
                      (RArray.leaf { law := 47, dual := 269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 48, dual := 259, proof := sorry })
                      (RArray.leaf { law := 49, dual := 279, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 50, dual := 289, proof := sorry })
                      (RArray.leaf { law := 51, dual := 256, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 52, dual := 272, proof := sorry })
                      (RArray.leaf { law := 53, dual := 275, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 54, dual := 262, proof := sorry })
                      (RArray.leaf { law := 55, dual := 282, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 56, dual := 297, proof := sorry })
                      (RArray.leaf { law := 57, dual := 265, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 58, dual := 293, proof := sorry })
                      (RArray.leaf { law := 59, dual := 285, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 60, dual := 301, proof := sorry })
                      (RArray.leaf { law := 61, dual := 255, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 62, dual := 270, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 63, dual := 271, proof := sorry })
                      (RArray.leaf { law := 64, dual := 260, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 65, dual := 280, proof := sorry })
                      (RArray.leaf { law := 66, dual := 291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 67, dual := 261, proof := sorry })
                      (RArray.leaf { law := 68, dual := 290, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 69, dual := 281, proof := sorry })
                      (RArray.leaf { law := 70, dual := 292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 71, dual := 257, proof := sorry })
                      (RArray.leaf { law := 72, dual := 273, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 73, dual := 277, proof := sorry })
                      (RArray.leaf { law := 74, dual := 263, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 75, dual := 283, proof := sorry })
                      (RArray.leaf { law := 76, dual := 299, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 77, dual := 267, proof := sorry })
                      (RArray.leaf { law := 78, dual := 294, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 79, dual := 287, proof := sorry })
                      (RArray.leaf { law := 80, dual := 304, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 81, dual := 258, proof := sorry })
                      (RArray.leaf { law := 82, dual := 276, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 83, dual := 274, proof := sorry })
                      (RArray.leaf { law := 84, dual := 278, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 85, dual := 266, proof := sorry })
                      (RArray.leaf { law := 86, dual := 286, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 87, dual := 295, proof := sorry })
                      (RArray.leaf { law := 88, dual := 303, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 89, dual := 264, proof := sorry })
                      (RArray.leaf { law := 90, dual := 298, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 91, dual := 284, proof := sorry })
                      (RArray.leaf { law := 92, dual := 300, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 93, dual := 268, proof := sorry })
                      (RArray.leaf { law := 94, dual := 302, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 95, dual := 296, proof := sorry })
                      (RArray.leaf { law := 96, dual := 288, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 97, dual := 305, proof := sorry })
                      (RArray.leaf { law := 98, dual := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 99, dual := 217, proof := sorry })
                      (RArray.leaf { law := 100, dual := 207, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 101, dual := 227, proof := sorry })
                      (RArray.leaf { law := 102, dual := 237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 103, dual := 204, proof := sorry })
                      (RArray.leaf { law := 104, dual := 220, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 105, dual := 223, proof := sorry })
                      (RArray.leaf { law := 106, dual := 210, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 107, dual := 230, proof := sorry })
                      (RArray.leaf { law := 108, dual := 245, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 109, dual := 213, proof := sorry })
                      (RArray.leaf { law := 110, dual := 241, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 111, dual := 233, proof := sorry })
                      (RArray.leaf { law := 112, dual := 249, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 113, dual := 203, proof := sorry })
                      (RArray.leaf { law := 114, dual := 218, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 115, dual := 219, proof := sorry })
                      (RArray.leaf { law := 116, dual := 208, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 117, dual := 228, proof := sorry })
                      (RArray.leaf { law := 118, dual := 239, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 119, dual := 209, proof := sorry })
                      (RArray.leaf { law := 120, dual := 238, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 121, dual := 229, proof := sorry })
                      (RArray.leaf { law := 122, dual := 240, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 123, dual := 205, proof := sorry })
                      (RArray.leaf { law := 124, dual := 221, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 125, dual := 225, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 126, dual := 211, proof := sorry })
                      (RArray.leaf { law := 127, dual := 231, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 128, dual := 247, proof := sorry })
                      (RArray.leaf { law := 129, dual := 215, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 130, dual := 242, proof := sorry })
                      (RArray.leaf { law := 131, dual := 235, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 132, dual := 252, proof := sorry })
                      (RArray.leaf { law := 133, dual := 206, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 134, dual := 224, proof := sorry })
                      (RArray.leaf { law := 135, dual := 222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 136, dual := 226, proof := sorry })
                      (RArray.leaf { law := 137, dual := 214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 138, dual := 234, proof := sorry })
                      (RArray.leaf { law := 139, dual := 243, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 140, dual := 251, proof := sorry })
                      (RArray.leaf { law := 141, dual := 212, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 142, dual := 246, proof := sorry })
                      (RArray.leaf { law := 143, dual := 232, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 144, dual := 248, proof := sorry })
                      (RArray.leaf { law := 145, dual := 216, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 146, dual := 250, proof := sorry })
                      (RArray.leaf { law := 147, dual := 244, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 148, dual := 236, proof := sorry })
                      (RArray.leaf { law := 149, dual := 253, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 150, dual := 150, proof := sorry })
                      (RArray.leaf { law := 151, dual := 165, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 152, dual := 155, proof := sorry })
                      (RArray.leaf { law := 153, dual := 175, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 154, dual := 185, proof := sorry })
                      (RArray.leaf { law := 155, dual := 152, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 156, dual := 168, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 157, dual := 171, proof := sorry })
                      (RArray.leaf { law := 158, dual := 158, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 159, dual := 178, proof := sorry })
                      (RArray.leaf { law := 160, dual := 193, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 161, dual := 161, proof := sorry })
                      (RArray.leaf { law := 162, dual := 189, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 163, dual := 181, proof := sorry })
                      (RArray.leaf { law := 164, dual := 197, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 165, dual := 151, proof := sorry })
                      (RArray.leaf { law := 166, dual := 166, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 167, dual := 167, proof := sorry })
                      (RArray.leaf { law := 168, dual := 156, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 169, dual := 176, proof := sorry })
                      (RArray.leaf { law := 170, dual := 187, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 171, dual := 157, proof := sorry })
                      (RArray.leaf { law := 172, dual := 186, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 173, dual := 177, proof := sorry })
                      (RArray.leaf { law := 174, dual := 188, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 175, dual := 153, proof := sorry })
                      (RArray.leaf { law := 176, dual := 169, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 177, dual := 173, proof := sorry })
                      (RArray.leaf { law := 178, dual := 159, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 179, dual := 179, proof := sorry })
                      (RArray.leaf { law := 180, dual := 195, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 181, dual := 163, proof := sorry })
                      (RArray.leaf { law := 182, dual := 190, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 183, dual := 183, proof := sorry })
                      (RArray.leaf { law := 184, dual := 200, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 185, dual := 154, proof := sorry })
                      (RArray.leaf { law := 186, dual := 172, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 187, dual := 170, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 188, dual := 174, proof := sorry })
                      (RArray.leaf { law := 189, dual := 162, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 190, dual := 182, proof := sorry })
                      (RArray.leaf { law := 191, dual := 191, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 192, dual := 199, proof := sorry })
                      (RArray.leaf { law := 193, dual := 160, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 194, dual := 194, proof := sorry })
                      (RArray.leaf { law := 195, dual := 180, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 196, dual := 196, proof := sorry })
                      (RArray.leaf { law := 197, dual := 164, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 198, dual := 198, proof := sorry })
                      (RArray.leaf { law := 199, dual := 192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 200, dual := 184, proof := sorry })
                      (RArray.leaf { law := 201, dual := 201, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 202, dual := 98, proof := sorry })
                      (RArray.leaf { law := 203, dual := 113, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 204, dual := 103, proof := sorry })
                      (RArray.leaf { law := 205, dual := 123, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 206, dual := 133, proof := sorry })
                      (RArray.leaf { law := 207, dual := 100, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 208, dual := 116, proof := sorry })
                      (RArray.leaf { law := 209, dual := 119, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 210, dual := 106, proof := sorry })
                      (RArray.leaf { law := 211, dual := 126, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 212, dual := 141, proof := sorry })
                      (RArray.leaf { law := 213, dual := 109, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 214, dual := 137, proof := sorry })
                      (RArray.leaf { law := 215, dual := 129, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 216, dual := 145, proof := sorry })
                      (RArray.leaf { law := 217, dual := 99, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 218, dual := 114, proof := sorry })
                      (RArray.leaf { law := 219, dual := 115, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 220, dual := 104, proof := sorry })
                      (RArray.leaf { law := 221, dual := 124, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 222, dual := 135, proof := sorry })
                      (RArray.leaf { law := 223, dual := 105, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 224, dual := 134, proof := sorry })
                      (RArray.leaf { law := 225, dual := 125, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 226, dual := 136, proof := sorry })
                      (RArray.leaf { law := 227, dual := 101, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 228, dual := 117, proof := sorry })
                      (RArray.leaf { law := 229, dual := 121, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 230, dual := 107, proof := sorry })
                      (RArray.leaf { law := 231, dual := 127, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 232, dual := 143, proof := sorry })
                      (RArray.leaf { law := 233, dual := 111, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 234, dual := 138, proof := sorry })
                      (RArray.leaf { law := 235, dual := 131, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 236, dual := 148, proof := sorry })
                      (RArray.leaf { law := 237, dual := 102, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 238, dual := 120, proof := sorry })
                      (RArray.leaf { law := 239, dual := 118, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 240, dual := 122, proof := sorry })
                      (RArray.leaf { law := 241, dual := 110, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 242, dual := 130, proof := sorry })
                      (RArray.leaf { law := 243, dual := 139, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 244, dual := 147, proof := sorry })
                      (RArray.leaf { law := 245, dual := 108, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 246, dual := 142, proof := sorry })
                      (RArray.leaf { law := 247, dual := 128, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 248, dual := 144, proof := sorry })
                      (RArray.leaf { law := 249, dual := 112, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 250, dual := 146, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 251, dual := 140, proof := sorry })
                      (RArray.leaf { law := 252, dual := 132, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 253, dual := 149, proof := sorry })
                      (RArray.leaf { law := 254, dual := 46, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 255, dual := 61, proof := sorry })
                      (RArray.leaf { law := 256, dual := 51, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 257, dual := 71, proof := sorry })
                      (RArray.leaf { law := 258, dual := 81, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 259, dual := 48, proof := sorry })
                      (RArray.leaf { law := 260, dual := 64, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 261, dual := 67, proof := sorry })
                      (RArray.leaf { law := 262, dual := 54, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 263, dual := 74, proof := sorry })
                      (RArray.leaf { law := 264, dual := 89, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 265, dual := 57, proof := sorry })
                      (RArray.leaf { law := 266, dual := 85, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 267, dual := 77, proof := sorry })
                      (RArray.leaf { law := 268, dual := 93, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 269, dual := 47, proof := sorry })
                      (RArray.leaf { law := 270, dual := 62, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 271, dual := 63, proof := sorry })
                      (RArray.leaf { law := 272, dual := 52, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 273, dual := 72, proof := sorry })
                      (RArray.leaf { law := 274, dual := 83, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 275, dual := 53, proof := sorry })
                      (RArray.leaf { law := 276, dual := 82, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 277, dual := 73, proof := sorry })
                      (RArray.leaf { law := 278, dual := 84, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 279, dual := 49, proof := sorry })
                      (RArray.leaf { law := 280, dual := 65, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 281, dual := 69, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 282, dual := 55, proof := sorry })
                      (RArray.leaf { law := 283, dual := 75, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 284, dual := 91, proof := sorry })
                      (RArray.leaf { law := 285, dual := 59, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 286, dual := 86, proof := sorry })
                      (RArray.leaf { law := 287, dual := 79, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 288, dual := 96, proof := sorry })
                      (RArray.leaf { law := 289, dual := 50, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 290, dual := 68, proof := sorry })
                      (RArray.leaf { law := 291, dual := 66, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 292, dual := 70, proof := sorry })
                      (RArray.leaf { law := 293, dual := 58, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 294, dual := 78, proof := sorry })
                      (RArray.leaf { law := 295, dual := 87, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 296, dual := 95, proof := sorry })
                      (RArray.leaf { law := 297, dual := 56, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 298, dual := 90, proof := sorry })
                      (RArray.leaf { law := 299, dual := 76, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 300, dual := 92, proof := sorry })
                      (RArray.leaf { law := 301, dual := 60, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 302, dual := 94, proof := sorry })
                      (RArray.leaf { law := 303, dual := 88, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 304, dual := 80, proof := sorry })
                      (RArray.leaf { law := 305, dual := 97, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 306, dual := 358, proof := sorry })
                      (RArray.leaf { law := 307, dual := 363, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 308, dual := 360, proof := sorry })
                      (RArray.leaf { law := 309, dual := 366, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 310, dual := 369, proof := sorry })
                      (RArray.leaf { law := 311, dual := 359, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 312, dual := 364, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 313, dual := 365, proof := sorry })
                      (RArray.leaf { law := 314, dual := 361, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 315, dual := 367, proof := sorry })
                      (RArray.leaf { law := 316, dual := 371, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 317, dual := 362, proof := sorry })
                      (RArray.leaf { law := 318, dual := 370, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 319, dual := 368, proof := sorry })
                      (RArray.leaf { law := 320, dual := 372, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 321, dual := 387, proof := sorry })
                      (RArray.leaf { law := 322, dual := 377, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 323, dual := 398, proof := sorry })
                      (RArray.leaf { law := 324, dual := 384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 325, dual := 374, proof := sorry })
                      (RArray.leaf { law := 326, dual := 394, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 327, dual := 390, proof := sorry })
                      (RArray.leaf { law := 328, dual := 380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 329, dual := 402, proof := sorry })
                      (RArray.leaf { law := 330, dual := 406, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 331, dual := 386, proof := sorry })
                      (RArray.leaf { law := 332, dual := 376, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 333, dual := 397, proof := sorry })
                      (RArray.leaf { law := 334, dual := 383, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 335, dual := 373, proof := sorry })
                      (RArray.leaf { law := 336, dual := 393, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 337, dual := 389, proof := sorry })
                      (RArray.leaf { law := 338, dual := 379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 339, dual := 401, proof := sorry })
                      (RArray.leaf { law := 340, dual := 405, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 341, dual := 388, proof := sorry })
                      (RArray.leaf { law := 342, dual := 378, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 343, dual := 399, proof := sorry })
                      (RArray.leaf { law := 344, dual := 400, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 345, dual := 385, proof := sorry })
                      (RArray.leaf { law := 346, dual := 375, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 347, dual := 395, proof := sorry })
                      (RArray.leaf { law := 348, dual := 396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 349, dual := 391, proof := sorry })
                      (RArray.leaf { law := 350, dual := 381, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 351, dual := 403, proof := sorry })
                      (RArray.leaf { law := 352, dual := 408, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 353, dual := 392, proof := sorry })
                      (RArray.leaf { law := 354, dual := 382, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 355, dual := 407, proof := sorry })
                      (RArray.leaf { law := 356, dual := 404, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 357, dual := 409, proof := sorry })
                      (RArray.leaf { law := 358, dual := 306, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 359, dual := 311, proof := sorry })
                      (RArray.leaf { law := 360, dual := 308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 361, dual := 314, proof := sorry })
                      (RArray.leaf { law := 362, dual := 317, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 363, dual := 307, proof := sorry })
                      (RArray.leaf { law := 364, dual := 312, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 365, dual := 313, proof := sorry })
                      (RArray.leaf { law := 366, dual := 309, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 367, dual := 315, proof := sorry })
                      (RArray.leaf { law := 368, dual := 319, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 369, dual := 310, proof := sorry })
                      (RArray.leaf { law := 370, dual := 318, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 371, dual := 316, proof := sorry })
                      (RArray.leaf { law := 372, dual := 320, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 373, dual := 335, proof := sorry })
                      (RArray.leaf { law := 374, dual := 325, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 375, dual := 346, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 376, dual := 332, proof := sorry })
                      (RArray.leaf { law := 377, dual := 322, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 378, dual := 342, proof := sorry })
                      (RArray.leaf { law := 379, dual := 338, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 380, dual := 328, proof := sorry })
                      (RArray.leaf { law := 381, dual := 350, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 382, dual := 354, proof := sorry })
                      (RArray.leaf { law := 383, dual := 334, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 384, dual := 324, proof := sorry })
                      (RArray.leaf { law := 385, dual := 345, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 386, dual := 331, proof := sorry })
                      (RArray.leaf { law := 387, dual := 321, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 388, dual := 341, proof := sorry })
                      (RArray.leaf { law := 389, dual := 337, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 390, dual := 327, proof := sorry })
                      (RArray.leaf { law := 391, dual := 349, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 392, dual := 353, proof := sorry })
                      (RArray.leaf { law := 393, dual := 336, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 394, dual := 326, proof := sorry })
                      (RArray.leaf { law := 395, dual := 347, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 396, dual := 348, proof := sorry })
                      (RArray.leaf { law := 397, dual := 333, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 398, dual := 323, proof := sorry })
                      (RArray.leaf { law := 399, dual := 343, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 400, dual := 344, proof := sorry })
                      (RArray.leaf { law := 401, dual := 339, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 402, dual := 329, proof := sorry })
                      (RArray.leaf { law := 403, dual := 351, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 404, dual := 356, proof := sorry })
                      (RArray.leaf { law := 405, dual := 340, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 406, dual := 330, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 407, dual := 355, proof := sorry })
                      (RArray.leaf { law := 408, dual := 352, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 409, dual := 357, proof := sorry })
                      (RArray.leaf { law := 410, dual := 3049, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 411, dual := 3101, proof := sorry })
                      (RArray.leaf { law := 412, dual := 3064, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 413, dual := 3138, proof := sorry })
                      (RArray.leaf { law := 414, dual := 3175, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 415, dual := 3054, proof := sorry })
                      (RArray.leaf { law := 416, dual := 3111, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 417, dual := 3121, proof := sorry })
                      (RArray.leaf { law := 418, dual := 3074, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 419, dual := 3148, proof := sorry })
                      (RArray.leaf { law := 420, dual := 3209, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 421, dual := 3084, proof := sorry })
                      (RArray.leaf { law := 422, dual := 3192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 423, dual := 3158, proof := sorry })
                      (RArray.leaf { law := 424, dual := 3226, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 425, dual := 3051, proof := sorry })
                      (RArray.leaf { law := 426, dual := 3104, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 427, dual := 3107, proof := sorry })
                      (RArray.leaf { law := 428, dual := 3067, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 429, dual := 3141, proof := sorry })
                      (RArray.leaf { law := 430, dual := 3183, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 431, dual := 3070, proof := sorry })
                      (RArray.leaf { law := 432, dual := 3179, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 433, dual := 3144, proof := sorry })
                      (RArray.leaf { law := 434, dual := 3187, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 435, dual := 3057, proof := sorry })
                      (RArray.leaf { law := 436, dual := 3114, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 437, dual := 3129, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 438, dual := 3077, proof := sorry })
                      (RArray.leaf { law := 439, dual := 3151, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 440, dual := 3217, proof := sorry })
                      (RArray.leaf { law := 441, dual := 3092, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 442, dual := 3196, proof := sorry })
                      (RArray.leaf { law := 443, dual := 3166, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 444, dual := 3241, proof := sorry })
                      (RArray.leaf { law := 445, dual := 3060, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 446, dual := 3125, proof := sorry })
                      (RArray.leaf { law := 447, dual := 3117, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 448, dual := 3133, proof := sorry })
                      (RArray.leaf { law := 449, dual := 3088, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 450, dual := 3162, proof := sorry })
                      (RArray.leaf { law := 451, dual := 3200, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 452, dual := 3236, proof := sorry })
                      (RArray.leaf { law := 453, dual := 3080, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 454, dual := 3213, proof := sorry })
                      (RArray.leaf { law := 455, dual := 3154, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 456, dual := 3221, proof := sorry })
                      (RArray.leaf { law := 457, dual := 3096, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 458, dual := 3231, proof := sorry })
                      (RArray.leaf { law := 459, dual := 3204, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 460, dual := 3170, proof := sorry })
                      (RArray.leaf { law := 461, dual := 3246, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 462, dual := 3050, proof := sorry })
                      (RArray.leaf { law := 463, dual := 3102, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 464, dual := 3103, proof := sorry })
                      (RArray.leaf { law := 465, dual := 3065, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 466, dual := 3139, proof := sorry })
                      (RArray.leaf { law := 467, dual := 3177, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 468, dual := 3066, proof := sorry })
                      (RArray.leaf { law := 469, dual := 3176, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 470, dual := 3140, proof := sorry })
                      (RArray.leaf { law := 471, dual := 3178, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 472, dual := 3055, proof := sorry })
                      (RArray.leaf { law := 473, dual := 3112, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 474, dual := 3123, proof := sorry })
                      (RArray.leaf { law := 475, dual := 3075, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 476, dual := 3149, proof := sorry })
                      (RArray.leaf { law := 477, dual := 3211, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 478, dual := 3086, proof := sorry })
                      (RArray.leaf { law := 479, dual := 3193, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 480, dual := 3160, proof := sorry })
                      (RArray.leaf { law := 481, dual := 3229, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 482, dual := 3056, proof := sorry })
                      (RArray.leaf { law := 483, dual := 3122, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 484, dual := 3113, proof := sorry })
                      (RArray.leaf { law := 485, dual := 3124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 486, dual := 3085, proof := sorry })
                      (RArray.leaf { law := 487, dual := 3159, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 488, dual := 3194, proof := sorry })
                      (RArray.leaf { law := 489, dual := 3228, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 490, dual := 3076, proof := sorry })
                      (RArray.leaf { law := 491, dual := 3210, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 492, dual := 3150, proof := sorry })
                      (RArray.leaf { law := 493, dual := 3212, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 494, dual := 3087, proof := sorry })
                      (RArray.leaf { law := 495, dual := 3227, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 496, dual := 3195, proof := sorry })
                      (RArray.leaf { law := 497, dual := 3161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 498, dual := 3230, proof := sorry })
                      (RArray.leaf { law := 499, dual := 3052, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 500, dual := 3105, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 501, dual := 3109, proof := sorry })
                      (RArray.leaf { law := 502, dual := 3068, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 503, dual := 3142, proof := sorry })
                      (RArray.leaf { law := 504, dual := 3185, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 505, dual := 3072, proof := sorry })
                      (RArray.leaf { law := 506, dual := 3180, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 507, dual := 3146, proof := sorry })
                      (RArray.leaf { law := 508, dual := 3190, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 509, dual := 3058, proof := sorry })
                      (RArray.leaf { law := 510, dual := 3115, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 511, dual := 3131, proof := sorry })
                      (RArray.leaf { law := 512, dual := 3078, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 513, dual := 3152, proof := sorry })
                      (RArray.leaf { law := 514, dual := 3219, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 515, dual := 3094, proof := sorry })
                      (RArray.leaf { law := 516, dual := 3197, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 517, dual := 3168, proof := sorry })
                      (RArray.leaf { law := 518, dual := 3244, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 519, dual := 3062, proof := sorry })
                      (RArray.leaf { law := 520, dual := 3126, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 521, dual := 3119, proof := sorry })
                      (RArray.leaf { law := 522, dual := 3136, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 523, dual := 3089, proof := sorry })
                      (RArray.leaf { law := 524, dual := 3163, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 525, dual := 3202, proof := sorry })
                      (RArray.leaf { law := 526, dual := 3238, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 527, dual := 3082, proof := sorry })
                      (RArray.leaf { law := 528, dual := 3214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 529, dual := 3156, proof := sorry })
                      (RArray.leaf { law := 530, dual := 3224, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 531, dual := 3099, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 532, dual := 3232, proof := sorry })
                      (RArray.leaf { law := 533, dual := 3207, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 534, dual := 3173, proof := sorry })
                      (RArray.leaf { law := 535, dual := 3250, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 536, dual := 3053, proof := sorry })
                      (RArray.leaf { law := 537, dual := 3108, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 538, dual := 3106, proof := sorry })
                      (RArray.leaf { law := 539, dual := 3110, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 540, dual := 3071, proof := sorry })
                      (RArray.leaf { law := 541, dual := 3145, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 542, dual := 3181, proof := sorry })
                      (RArray.leaf { law := 543, dual := 3189, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 544, dual := 3069, proof := sorry })
                      (RArray.leaf { law := 545, dual := 3184, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 546, dual := 3143, proof := sorry })
                      (RArray.leaf { law := 547, dual := 3186, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 548, dual := 3073, proof := sorry })
                      (RArray.leaf { law := 549, dual := 3188, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 550, dual := 3182, proof := sorry })
                      (RArray.leaf { law := 551, dual := 3147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 552, dual := 3191, proof := sorry })
                      (RArray.leaf { law := 553, dual := 3061, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 554, dual := 3118, proof := sorry })
                      (RArray.leaf { law := 555, dual := 3127, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 556, dual := 3135, proof := sorry })
                      (RArray.leaf { law := 557, dual := 3081, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 558, dual := 3155, proof := sorry })
                      (RArray.leaf { law := 559, dual := 3215, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 560, dual := 3223, proof := sorry })
                      (RArray.leaf { law := 561, dual := 3090, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 562, dual := 3201, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 563, dual := 3164, proof := sorry })
                      (RArray.leaf { law := 564, dual := 3239, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 565, dual := 3098, proof := sorry })
                      (RArray.leaf { law := 566, dual := 3205, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 567, dual := 3234, proof := sorry })
                      (RArray.leaf { law := 568, dual := 3172, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 569, dual := 3249, proof := sorry })
                      (RArray.leaf { law := 570, dual := 3059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 571, dual := 3130, proof := sorry })
                      (RArray.leaf { law := 572, dual := 3116, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 573, dual := 3132, proof := sorry })
                      (RArray.leaf { law := 574, dual := 3093, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 575, dual := 3167, proof := sorry })
                      (RArray.leaf { law := 576, dual := 3198, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 577, dual := 3243, proof := sorry })
                      (RArray.leaf { law := 578, dual := 3079, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 579, dual := 3218, proof := sorry })
                      (RArray.leaf { law := 580, dual := 3153, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 581, dual := 3220, proof := sorry })
                      (RArray.leaf { law := 582, dual := 3095, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 583, dual := 3242, proof := sorry })
                      (RArray.leaf { law := 584, dual := 3199, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 585, dual := 3169, proof := sorry })
                      (RArray.leaf { law := 586, dual := 3245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 587, dual := 3063, proof := sorry })
                      (RArray.leaf { law := 588, dual := 3134, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 589, dual := 3128, proof := sorry })
                      (RArray.leaf { law := 590, dual := 3120, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 591, dual := 3137, proof := sorry })
                      (RArray.leaf { law := 592, dual := 3097, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 593, dual := 3171, proof := sorry })
                      (RArray.leaf { law := 594, dual := 3233, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 595, dual := 3206, proof := sorry })
                      (RArray.leaf { law := 596, dual := 3248, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 597, dual := 3091, proof := sorry })
                      (RArray.leaf { law := 598, dual := 3237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 599, dual := 3165, proof := sorry })
                      (RArray.leaf { law := 600, dual := 3203, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 601, dual := 3240, proof := sorry })
                      (RArray.leaf { law := 602, dual := 3083, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 603, dual := 3222, proof := sorry })
                      (RArray.leaf { law := 604, dual := 3216, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 605, dual := 3157, proof := sorry })
                      (RArray.leaf { law := 606, dual := 3225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 607, dual := 3100, proof := sorry })
                      (RArray.leaf { law := 608, dual := 3247, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 609, dual := 3235, proof := sorry })
                      (RArray.leaf { law := 610, dual := 3208, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 611, dual := 3174, proof := sorry })
                      (RArray.leaf { law := 612, dual := 3251, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 613, dual := 2846, proof := sorry })
                      (RArray.leaf { law := 614, dual := 2898, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 615, dual := 2861, proof := sorry })
                      (RArray.leaf { law := 616, dual := 2935, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 617, dual := 2972, proof := sorry })
                      (RArray.leaf { law := 618, dual := 2851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 619, dual := 2908, proof := sorry })
                      (RArray.leaf { law := 620, dual := 2918, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 621, dual := 2871, proof := sorry })
                      (RArray.leaf { law := 622, dual := 2945, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 623, dual := 3006, proof := sorry })
                      (RArray.leaf { law := 624, dual := 2881, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 625, dual := 2989, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 626, dual := 2955, proof := sorry })
                      (RArray.leaf { law := 627, dual := 3023, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 628, dual := 2848, proof := sorry })
                      (RArray.leaf { law := 629, dual := 2901, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 630, dual := 2904, proof := sorry })
                      (RArray.leaf { law := 631, dual := 2864, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 632, dual := 2938, proof := sorry })
                      (RArray.leaf { law := 633, dual := 2980, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 634, dual := 2867, proof := sorry })
                      (RArray.leaf { law := 635, dual := 2976, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 636, dual := 2941, proof := sorry })
                      (RArray.leaf { law := 637, dual := 2984, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 638, dual := 2854, proof := sorry })
                      (RArray.leaf { law := 639, dual := 2911, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 640, dual := 2926, proof := sorry })
                      (RArray.leaf { law := 641, dual := 2874, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 642, dual := 2948, proof := sorry })
                      (RArray.leaf { law := 643, dual := 3014, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 644, dual := 2889, proof := sorry })
                      (RArray.leaf { law := 645, dual := 2993, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 646, dual := 2963, proof := sorry })
                      (RArray.leaf { law := 647, dual := 3038, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 648, dual := 2857, proof := sorry })
                      (RArray.leaf { law := 649, dual := 2922, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 650, dual := 2914, proof := sorry })
                      (RArray.leaf { law := 651, dual := 2930, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 652, dual := 2885, proof := sorry })
                      (RArray.leaf { law := 653, dual := 2959, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 654, dual := 2997, proof := sorry })
                      (RArray.leaf { law := 655, dual := 3033, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 656, dual := 2877, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 657, dual := 3010, proof := sorry })
                      (RArray.leaf { law := 658, dual := 2951, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 659, dual := 3018, proof := sorry })
                      (RArray.leaf { law := 660, dual := 2893, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 661, dual := 3028, proof := sorry })
                      (RArray.leaf { law := 662, dual := 3001, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 663, dual := 2967, proof := sorry })
                      (RArray.leaf { law := 664, dual := 3043, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 665, dual := 2847, proof := sorry })
                      (RArray.leaf { law := 666, dual := 2899, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 667, dual := 2900, proof := sorry })
                      (RArray.leaf { law := 668, dual := 2862, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 669, dual := 2936, proof := sorry })
                      (RArray.leaf { law := 670, dual := 2974, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 671, dual := 2863, proof := sorry })
                      (RArray.leaf { law := 672, dual := 2973, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 673, dual := 2937, proof := sorry })
                      (RArray.leaf { law := 674, dual := 2975, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 675, dual := 2852, proof := sorry })
                      (RArray.leaf { law := 676, dual := 2909, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 677, dual := 2920, proof := sorry })
                      (RArray.leaf { law := 678, dual := 2872, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 679, dual := 2946, proof := sorry })
                      (RArray.leaf { law := 680, dual := 3008, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 681, dual := 2883, proof := sorry })
                      (RArray.leaf { law := 682, dual := 2990, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 683, dual := 2957, proof := sorry })
                      (RArray.leaf { law := 684, dual := 3026, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 685, dual := 2853, proof := sorry })
                      (RArray.leaf { law := 686, dual := 2919, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 687, dual := 2910, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 688, dual := 2921, proof := sorry })
                      (RArray.leaf { law := 689, dual := 2882, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 690, dual := 2956, proof := sorry })
                      (RArray.leaf { law := 691, dual := 2991, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 692, dual := 3025, proof := sorry })
                      (RArray.leaf { law := 693, dual := 2873, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 694, dual := 3007, proof := sorry })
                      (RArray.leaf { law := 695, dual := 2947, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 696, dual := 3009, proof := sorry })
                      (RArray.leaf { law := 697, dual := 2884, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 698, dual := 3024, proof := sorry })
                      (RArray.leaf { law := 699, dual := 2992, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 700, dual := 2958, proof := sorry })
                      (RArray.leaf { law := 701, dual := 3027, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 702, dual := 2849, proof := sorry })
                      (RArray.leaf { law := 703, dual := 2902, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 704, dual := 2906, proof := sorry })
                      (RArray.leaf { law := 705, dual := 2865, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 706, dual := 2939, proof := sorry })
                      (RArray.leaf { law := 707, dual := 2982, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 708, dual := 2869, proof := sorry })
                      (RArray.leaf { law := 709, dual := 2977, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 710, dual := 2943, proof := sorry })
                      (RArray.leaf { law := 711, dual := 2987, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 712, dual := 2855, proof := sorry })
                      (RArray.leaf { law := 713, dual := 2912, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 714, dual := 2928, proof := sorry })
                      (RArray.leaf { law := 715, dual := 2875, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 716, dual := 2949, proof := sorry })
                      (RArray.leaf { law := 717, dual := 3016, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 718, dual := 2891, proof := sorry })
                      (RArray.leaf { law := 719, dual := 2994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 720, dual := 2965, proof := sorry })
                      (RArray.leaf { law := 721, dual := 3041, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 722, dual := 2859, proof := sorry })
                      (RArray.leaf { law := 723, dual := 2923, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 724, dual := 2916, proof := sorry })
                      (RArray.leaf { law := 725, dual := 2933, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 726, dual := 2886, proof := sorry })
                      (RArray.leaf { law := 727, dual := 2960, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 728, dual := 2999, proof := sorry })
                      (RArray.leaf { law := 729, dual := 3035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 730, dual := 2879, proof := sorry })
                      (RArray.leaf { law := 731, dual := 3011, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 732, dual := 2953, proof := sorry })
                      (RArray.leaf { law := 733, dual := 3021, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 734, dual := 2896, proof := sorry })
                      (RArray.leaf { law := 735, dual := 3029, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 736, dual := 3004, proof := sorry })
                      (RArray.leaf { law := 737, dual := 2970, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 738, dual := 3047, proof := sorry })
                      (RArray.leaf { law := 739, dual := 2850, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 740, dual := 2905, proof := sorry })
                      (RArray.leaf { law := 741, dual := 2903, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 742, dual := 2907, proof := sorry })
                      (RArray.leaf { law := 743, dual := 2868, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 744, dual := 2942, proof := sorry })
                      (RArray.leaf { law := 745, dual := 2978, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 746, dual := 2986, proof := sorry })
                      (RArray.leaf { law := 747, dual := 2866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 748, dual := 2981, proof := sorry })
                      (RArray.leaf { law := 749, dual := 2940, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 750, dual := 2983, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 751, dual := 2870, proof := sorry })
                      (RArray.leaf { law := 752, dual := 2985, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 753, dual := 2979, proof := sorry })
                      (RArray.leaf { law := 754, dual := 2944, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 755, dual := 2988, proof := sorry })
                      (RArray.leaf { law := 756, dual := 2858, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 757, dual := 2915, proof := sorry })
                      (RArray.leaf { law := 758, dual := 2924, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 759, dual := 2932, proof := sorry })
                      (RArray.leaf { law := 760, dual := 2878, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 761, dual := 2952, proof := sorry })
                      (RArray.leaf { law := 762, dual := 3012, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 763, dual := 3020, proof := sorry })
                      (RArray.leaf { law := 764, dual := 2887, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 765, dual := 2998, proof := sorry })
                      (RArray.leaf { law := 766, dual := 2961, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 767, dual := 3036, proof := sorry })
                      (RArray.leaf { law := 768, dual := 2895, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 769, dual := 3002, proof := sorry })
                      (RArray.leaf { law := 770, dual := 3031, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 771, dual := 2969, proof := sorry })
                      (RArray.leaf { law := 772, dual := 3046, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 773, dual := 2856, proof := sorry })
                      (RArray.leaf { law := 774, dual := 2927, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 775, dual := 2913, proof := sorry })
                      (RArray.leaf { law := 776, dual := 2929, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 777, dual := 2890, proof := sorry })
                      (RArray.leaf { law := 778, dual := 2964, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 779, dual := 2995, proof := sorry })
                      (RArray.leaf { law := 780, dual := 3040, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 781, dual := 2876, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 782, dual := 3015, proof := sorry })
                      (RArray.leaf { law := 783, dual := 2950, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 784, dual := 3017, proof := sorry })
                      (RArray.leaf { law := 785, dual := 2892, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 786, dual := 3039, proof := sorry })
                      (RArray.leaf { law := 787, dual := 2996, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 788, dual := 2966, proof := sorry })
                      (RArray.leaf { law := 789, dual := 3042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 790, dual := 2860, proof := sorry })
                      (RArray.leaf { law := 791, dual := 2931, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 792, dual := 2925, proof := sorry })
                      (RArray.leaf { law := 793, dual := 2917, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 794, dual := 2934, proof := sorry })
                      (RArray.leaf { law := 795, dual := 2894, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 796, dual := 2968, proof := sorry })
                      (RArray.leaf { law := 797, dual := 3030, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 798, dual := 3003, proof := sorry })
                      (RArray.leaf { law := 799, dual := 3045, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 800, dual := 2888, proof := sorry })
                      (RArray.leaf { law := 801, dual := 3034, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 802, dual := 2962, proof := sorry })
                      (RArray.leaf { law := 803, dual := 3000, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 804, dual := 3037, proof := sorry })
                      (RArray.leaf { law := 805, dual := 2880, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 806, dual := 3019, proof := sorry })
                      (RArray.leaf { law := 807, dual := 3013, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 808, dual := 2954, proof := sorry })
                      (RArray.leaf { law := 809, dual := 3022, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 810, dual := 2897, proof := sorry })
                      (RArray.leaf { law := 811, dual := 3044, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 812, dual := 3032, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 813, dual := 3005, proof := sorry })
                      (RArray.leaf { law := 814, dual := 2971, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 815, dual := 3048, proof := sorry })
                      (RArray.leaf { law := 816, dual := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 817, dual := 2695, proof := sorry })
                      (RArray.leaf { law := 818, dual := 2658, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 819, dual := 2732, proof := sorry })
                      (RArray.leaf { law := 820, dual := 2769, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 821, dual := 2648, proof := sorry })
                      (RArray.leaf { law := 822, dual := 2705, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 823, dual := 2715, proof := sorry })
                      (RArray.leaf { law := 824, dual := 2668, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 825, dual := 2742, proof := sorry })
                      (RArray.leaf { law := 826, dual := 2803, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 827, dual := 2678, proof := sorry })
                      (RArray.leaf { law := 828, dual := 2786, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 829, dual := 2752, proof := sorry })
                      (RArray.leaf { law := 830, dual := 2820, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 831, dual := 2645, proof := sorry })
                      (RArray.leaf { law := 832, dual := 2698, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 833, dual := 2701, proof := sorry })
                      (RArray.leaf { law := 834, dual := 2661, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 835, dual := 2735, proof := sorry })
                      (RArray.leaf { law := 836, dual := 2777, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 837, dual := 2664, proof := sorry })
                      (RArray.leaf { law := 838, dual := 2773, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 839, dual := 2738, proof := sorry })
                      (RArray.leaf { law := 840, dual := 2781, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 841, dual := 2651, proof := sorry })
                      (RArray.leaf { law := 842, dual := 2708, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 843, dual := 2723, proof := sorry })
                      (RArray.leaf { law := 844, dual := 2671, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 845, dual := 2745, proof := sorry })
                      (RArray.leaf { law := 846, dual := 2811, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 847, dual := 2686, proof := sorry })
                      (RArray.leaf { law := 848, dual := 2790, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 849, dual := 2760, proof := sorry })
                      (RArray.leaf { law := 850, dual := 2835, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 851, dual := 2654, proof := sorry })
                      (RArray.leaf { law := 852, dual := 2719, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 853, dual := 2711, proof := sorry })
                      (RArray.leaf { law := 854, dual := 2727, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 855, dual := 2682, proof := sorry })
                      (RArray.leaf { law := 856, dual := 2756, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 857, dual := 2794, proof := sorry })
                      (RArray.leaf { law := 858, dual := 2830, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 859, dual := 2674, proof := sorry })
                      (RArray.leaf { law := 860, dual := 2807, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 861, dual := 2748, proof := sorry })
                      (RArray.leaf { law := 862, dual := 2815, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 863, dual := 2690, proof := sorry })
                      (RArray.leaf { law := 864, dual := 2825, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 865, dual := 2798, proof := sorry })
                      (RArray.leaf { law := 866, dual := 2764, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 867, dual := 2840, proof := sorry })
                      (RArray.leaf { law := 868, dual := 2644, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 869, dual := 2696, proof := sorry })
                      (RArray.leaf { law := 870, dual := 2697, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 871, dual := 2659, proof := sorry })
                      (RArray.leaf { law := 872, dual := 2733, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 873, dual := 2771, proof := sorry })
                      (RArray.leaf { law := 874, dual := 2660, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 875, dual := 2770, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 876, dual := 2734, proof := sorry })
                      (RArray.leaf { law := 877, dual := 2772, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 878, dual := 2649, proof := sorry })
                      (RArray.leaf { law := 879, dual := 2706, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 880, dual := 2717, proof := sorry })
                      (RArray.leaf { law := 881, dual := 2669, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 882, dual := 2743, proof := sorry })
                      (RArray.leaf { law := 883, dual := 2805, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 884, dual := 2680, proof := sorry })
                      (RArray.leaf { law := 885, dual := 2787, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 886, dual := 2754, proof := sorry })
                      (RArray.leaf { law := 887, dual := 2823, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 888, dual := 2650, proof := sorry })
                      (RArray.leaf { law := 889, dual := 2716, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 890, dual := 2707, proof := sorry })
                      (RArray.leaf { law := 891, dual := 2718, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 892, dual := 2679, proof := sorry })
                      (RArray.leaf { law := 893, dual := 2753, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 894, dual := 2788, proof := sorry })
                      (RArray.leaf { law := 895, dual := 2822, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 896, dual := 2670, proof := sorry })
                      (RArray.leaf { law := 897, dual := 2804, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 898, dual := 2744, proof := sorry })
                      (RArray.leaf { law := 899, dual := 2806, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 900, dual := 2681, proof := sorry })
                      (RArray.leaf { law := 901, dual := 2821, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 902, dual := 2789, proof := sorry })
                      (RArray.leaf { law := 903, dual := 2755, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 904, dual := 2824, proof := sorry })
                      (RArray.leaf { law := 905, dual := 2646, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 906, dual := 2699, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 907, dual := 2703, proof := sorry })
                      (RArray.leaf { law := 908, dual := 2662, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 909, dual := 2736, proof := sorry })
                      (RArray.leaf { law := 910, dual := 2779, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 911, dual := 2666, proof := sorry })
                      (RArray.leaf { law := 912, dual := 2774, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 913, dual := 2740, proof := sorry })
                      (RArray.leaf { law := 914, dual := 2784, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 915, dual := 2652, proof := sorry })
                      (RArray.leaf { law := 916, dual := 2709, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 917, dual := 2725, proof := sorry })
                      (RArray.leaf { law := 918, dual := 2672, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 919, dual := 2746, proof := sorry })
                      (RArray.leaf { law := 920, dual := 2813, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 921, dual := 2688, proof := sorry })
                      (RArray.leaf { law := 922, dual := 2791, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 923, dual := 2762, proof := sorry })
                      (RArray.leaf { law := 924, dual := 2838, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 925, dual := 2656, proof := sorry })
                      (RArray.leaf { law := 926, dual := 2720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 927, dual := 2713, proof := sorry })
                      (RArray.leaf { law := 928, dual := 2730, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 929, dual := 2683, proof := sorry })
                      (RArray.leaf { law := 930, dual := 2757, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 931, dual := 2796, proof := sorry })
                      (RArray.leaf { law := 932, dual := 2832, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 933, dual := 2676, proof := sorry })
                      (RArray.leaf { law := 934, dual := 2808, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 935, dual := 2750, proof := sorry })
                      (RArray.leaf { law := 936, dual := 2818, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 937, dual := 2693, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 938, dual := 2826, proof := sorry })
                      (RArray.leaf { law := 939, dual := 2801, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 940, dual := 2767, proof := sorry })
                      (RArray.leaf { law := 941, dual := 2844, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 942, dual := 2647, proof := sorry })
                      (RArray.leaf { law := 943, dual := 2702, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 944, dual := 2700, proof := sorry })
                      (RArray.leaf { law := 945, dual := 2704, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 946, dual := 2665, proof := sorry })
                      (RArray.leaf { law := 947, dual := 2739, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 948, dual := 2775, proof := sorry })
                      (RArray.leaf { law := 949, dual := 2783, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 950, dual := 2663, proof := sorry })
                      (RArray.leaf { law := 951, dual := 2778, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 952, dual := 2737, proof := sorry })
                      (RArray.leaf { law := 953, dual := 2780, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 954, dual := 2667, proof := sorry })
                      (RArray.leaf { law := 955, dual := 2782, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 956, dual := 2776, proof := sorry })
                      (RArray.leaf { law := 957, dual := 2741, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 958, dual := 2785, proof := sorry })
                      (RArray.leaf { law := 959, dual := 2655, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 960, dual := 2712, proof := sorry })
                      (RArray.leaf { law := 961, dual := 2721, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 962, dual := 2729, proof := sorry })
                      (RArray.leaf { law := 963, dual := 2675, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 964, dual := 2749, proof := sorry })
                      (RArray.leaf { law := 965, dual := 2809, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 966, dual := 2817, proof := sorry })
                      (RArray.leaf { law := 967, dual := 2684, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 968, dual := 2795, proof := sorry })
                      (RArray.leaf { law := 969, dual := 2758, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 970, dual := 2833, proof := sorry })
                      (RArray.leaf { law := 971, dual := 2692, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 972, dual := 2799, proof := sorry })
                      (RArray.leaf { law := 973, dual := 2828, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 974, dual := 2766, proof := sorry })
                      (RArray.leaf { law := 975, dual := 2843, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 976, dual := 2653, proof := sorry })
                      (RArray.leaf { law := 977, dual := 2724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 978, dual := 2710, proof := sorry })
                      (RArray.leaf { law := 979, dual := 2726, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 980, dual := 2687, proof := sorry })
                      (RArray.leaf { law := 981, dual := 2761, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 982, dual := 2792, proof := sorry })
                      (RArray.leaf { law := 983, dual := 2837, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 984, dual := 2673, proof := sorry })
                      (RArray.leaf { law := 985, dual := 2812, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 986, dual := 2747, proof := sorry })
                      (RArray.leaf { law := 987, dual := 2814, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 988, dual := 2689, proof := sorry })
                      (RArray.leaf { law := 989, dual := 2836, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 990, dual := 2793, proof := sorry })
                      (RArray.leaf { law := 991, dual := 2763, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 992, dual := 2839, proof := sorry })
                      (RArray.leaf { law := 993, dual := 2657, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 994, dual := 2728, proof := sorry })
                      (RArray.leaf { law := 995, dual := 2722, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 996, dual := 2714, proof := sorry })
                      (RArray.leaf { law := 997, dual := 2731, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 998, dual := 2691, proof := sorry })
                      (RArray.leaf { law := 999, dual := 2765, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1000, dual := 2827, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1001, dual := 2800, proof := sorry })
                      (RArray.leaf { law := 1002, dual := 2842, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1003, dual := 2685, proof := sorry })
                      (RArray.leaf { law := 1004, dual := 2831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1005, dual := 2759, proof := sorry })
                      (RArray.leaf { law := 1006, dual := 2797, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1007, dual := 2834, proof := sorry })
                      (RArray.leaf { law := 1008, dual := 2677, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1009, dual := 2816, proof := sorry })
                      (RArray.leaf { law := 1010, dual := 2810, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1011, dual := 2751, proof := sorry })
                      (RArray.leaf { law := 1012, dual := 2819, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1013, dual := 2694, proof := sorry })
                      (RArray.leaf { law := 1014, dual := 2841, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1015, dual := 2829, proof := sorry })
                      (RArray.leaf { law := 1016, dual := 2802, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1017, dual := 2768, proof := sorry })
                      (RArray.leaf { law := 1018, dual := 2845, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1019, dual := 2440, proof := sorry })
                      (RArray.leaf { law := 1020, dual := 2492, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1021, dual := 2455, proof := sorry })
                      (RArray.leaf { law := 1022, dual := 2529, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1023, dual := 2566, proof := sorry })
                      (RArray.leaf { law := 1024, dual := 2445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1025, dual := 2502, proof := sorry })
                      (RArray.leaf { law := 1026, dual := 2512, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1027, dual := 2465, proof := sorry })
                      (RArray.leaf { law := 1028, dual := 2539, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1029, dual := 2600, proof := sorry })
                      (RArray.leaf { law := 1030, dual := 2475, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1031, dual := 2583, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1032, dual := 2549, proof := sorry })
                      (RArray.leaf { law := 1033, dual := 2617, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1034, dual := 2442, proof := sorry })
                      (RArray.leaf { law := 1035, dual := 2495, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1036, dual := 2498, proof := sorry })
                      (RArray.leaf { law := 1037, dual := 2458, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1038, dual := 2532, proof := sorry })
                      (RArray.leaf { law := 1039, dual := 2574, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1040, dual := 2461, proof := sorry })
                      (RArray.leaf { law := 1041, dual := 2570, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1042, dual := 2535, proof := sorry })
                      (RArray.leaf { law := 1043, dual := 2578, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1044, dual := 2448, proof := sorry })
                      (RArray.leaf { law := 1045, dual := 2505, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1046, dual := 2520, proof := sorry })
                      (RArray.leaf { law := 1047, dual := 2468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1048, dual := 2542, proof := sorry })
                      (RArray.leaf { law := 1049, dual := 2608, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1050, dual := 2483, proof := sorry })
                      (RArray.leaf { law := 1051, dual := 2587, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1052, dual := 2557, proof := sorry })
                      (RArray.leaf { law := 1053, dual := 2632, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1054, dual := 2451, proof := sorry })
                      (RArray.leaf { law := 1055, dual := 2516, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1056, dual := 2508, proof := sorry })
                      (RArray.leaf { law := 1057, dual := 2524, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1058, dual := 2479, proof := sorry })
                      (RArray.leaf { law := 1059, dual := 2553, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1060, dual := 2591, proof := sorry })
                      (RArray.leaf { law := 1061, dual := 2627, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1062, dual := 2471, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1063, dual := 2604, proof := sorry })
                      (RArray.leaf { law := 1064, dual := 2545, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1065, dual := 2612, proof := sorry })
                      (RArray.leaf { law := 1066, dual := 2487, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1067, dual := 2622, proof := sorry })
                      (RArray.leaf { law := 1068, dual := 2595, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1069, dual := 2561, proof := sorry })
                      (RArray.leaf { law := 1070, dual := 2637, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1071, dual := 2441, proof := sorry })
                      (RArray.leaf { law := 1072, dual := 2493, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1073, dual := 2494, proof := sorry })
                      (RArray.leaf { law := 1074, dual := 2456, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1075, dual := 2530, proof := sorry })
                      (RArray.leaf { law := 1076, dual := 2568, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1077, dual := 2457, proof := sorry })
                      (RArray.leaf { law := 1078, dual := 2567, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1079, dual := 2531, proof := sorry })
                      (RArray.leaf { law := 1080, dual := 2569, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1081, dual := 2446, proof := sorry })
                      (RArray.leaf { law := 1082, dual := 2503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1083, dual := 2514, proof := sorry })
                      (RArray.leaf { law := 1084, dual := 2466, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1085, dual := 2540, proof := sorry })
                      (RArray.leaf { law := 1086, dual := 2602, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1087, dual := 2477, proof := sorry })
                      (RArray.leaf { law := 1088, dual := 2584, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1089, dual := 2551, proof := sorry })
                      (RArray.leaf { law := 1090, dual := 2620, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1091, dual := 2447, proof := sorry })
                      (RArray.leaf { law := 1092, dual := 2513, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1093, dual := 2504, proof := sorry })
                      (RArray.leaf { law := 1094, dual := 2515, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1095, dual := 2476, proof := sorry })
                      (RArray.leaf { law := 1096, dual := 2550, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1097, dual := 2585, proof := sorry })
                      (RArray.leaf { law := 1098, dual := 2619, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1099, dual := 2467, proof := sorry })
                      (RArray.leaf { law := 1100, dual := 2601, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1101, dual := 2541, proof := sorry })
                      (RArray.leaf { law := 1102, dual := 2603, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1103, dual := 2478, proof := sorry })
                      (RArray.leaf { law := 1104, dual := 2618, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1105, dual := 2586, proof := sorry })
                      (RArray.leaf { law := 1106, dual := 2552, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1107, dual := 2621, proof := sorry })
                      (RArray.leaf { law := 1108, dual := 2443, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1109, dual := 2496, proof := sorry })
                      (RArray.leaf { law := 1110, dual := 2500, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1111, dual := 2459, proof := sorry })
                      (RArray.leaf { law := 1112, dual := 2533, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1113, dual := 2576, proof := sorry })
                      (RArray.leaf { law := 1114, dual := 2463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1115, dual := 2571, proof := sorry })
                      (RArray.leaf { law := 1116, dual := 2537, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1117, dual := 2581, proof := sorry })
                      (RArray.leaf { law := 1118, dual := 2449, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1119, dual := 2506, proof := sorry })
                      (RArray.leaf { law := 1120, dual := 2522, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1121, dual := 2469, proof := sorry })
                      (RArray.leaf { law := 1122, dual := 2543, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1123, dual := 2610, proof := sorry })
                      (RArray.leaf { law := 1124, dual := 2485, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1125, dual := 2588, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1126, dual := 2559, proof := sorry })
                      (RArray.leaf { law := 1127, dual := 2635, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1128, dual := 2453, proof := sorry })
                      (RArray.leaf { law := 1129, dual := 2517, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1130, dual := 2510, proof := sorry })
                      (RArray.leaf { law := 1131, dual := 2527, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1132, dual := 2480, proof := sorry })
                      (RArray.leaf { law := 1133, dual := 2554, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1134, dual := 2593, proof := sorry })
                      (RArray.leaf { law := 1135, dual := 2629, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1136, dual := 2473, proof := sorry })
                      (RArray.leaf { law := 1137, dual := 2605, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1138, dual := 2547, proof := sorry })
                      (RArray.leaf { law := 1139, dual := 2615, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1140, dual := 2490, proof := sorry })
                      (RArray.leaf { law := 1141, dual := 2623, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1142, dual := 2598, proof := sorry })
                      (RArray.leaf { law := 1143, dual := 2564, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1144, dual := 2641, proof := sorry })
                      (RArray.leaf { law := 1145, dual := 2444, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1146, dual := 2499, proof := sorry })
                      (RArray.leaf { law := 1147, dual := 2497, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1148, dual := 2501, proof := sorry })
                      (RArray.leaf { law := 1149, dual := 2462, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1150, dual := 2536, proof := sorry })
                      (RArray.leaf { law := 1151, dual := 2572, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1152, dual := 2580, proof := sorry })
                      (RArray.leaf { law := 1153, dual := 2460, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1154, dual := 2575, proof := sorry })
                      (RArray.leaf { law := 1155, dual := 2534, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1156, dual := 2577, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1157, dual := 2464, proof := sorry })
                      (RArray.leaf { law := 1158, dual := 2579, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1159, dual := 2573, proof := sorry })
                      (RArray.leaf { law := 1160, dual := 2538, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1161, dual := 2582, proof := sorry })
                      (RArray.leaf { law := 1162, dual := 2452, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1163, dual := 2509, proof := sorry })
                      (RArray.leaf { law := 1164, dual := 2518, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1165, dual := 2526, proof := sorry })
                      (RArray.leaf { law := 1166, dual := 2472, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1167, dual := 2546, proof := sorry })
                      (RArray.leaf { law := 1168, dual := 2606, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1169, dual := 2614, proof := sorry })
                      (RArray.leaf { law := 1170, dual := 2481, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1171, dual := 2592, proof := sorry })
                      (RArray.leaf { law := 1172, dual := 2555, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1173, dual := 2630, proof := sorry })
                      (RArray.leaf { law := 1174, dual := 2489, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1175, dual := 2596, proof := sorry })
                      (RArray.leaf { law := 1176, dual := 2625, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1177, dual := 2563, proof := sorry })
                      (RArray.leaf { law := 1178, dual := 2640, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1179, dual := 2450, proof := sorry })
                      (RArray.leaf { law := 1180, dual := 2521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1181, dual := 2507, proof := sorry })
                      (RArray.leaf { law := 1182, dual := 2523, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1183, dual := 2484, proof := sorry })
                      (RArray.leaf { law := 1184, dual := 2558, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1185, dual := 2589, proof := sorry })
                      (RArray.leaf { law := 1186, dual := 2634, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1187, dual := 2470, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1188, dual := 2609, proof := sorry })
                      (RArray.leaf { law := 1189, dual := 2544, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1190, dual := 2611, proof := sorry })
                      (RArray.leaf { law := 1191, dual := 2486, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1192, dual := 2633, proof := sorry })
                      (RArray.leaf { law := 1193, dual := 2590, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1194, dual := 2560, proof := sorry })
                      (RArray.leaf { law := 1195, dual := 2636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1196, dual := 2454, proof := sorry })
                      (RArray.leaf { law := 1197, dual := 2525, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1198, dual := 2519, proof := sorry })
                      (RArray.leaf { law := 1199, dual := 2511, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1200, dual := 2528, proof := sorry })
                      (RArray.leaf { law := 1201, dual := 2488, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1202, dual := 2562, proof := sorry })
                      (RArray.leaf { law := 1203, dual := 2624, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1204, dual := 2597, proof := sorry })
                      (RArray.leaf { law := 1205, dual := 2639, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1206, dual := 2482, proof := sorry })
                      (RArray.leaf { law := 1207, dual := 2628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1208, dual := 2556, proof := sorry })
                      (RArray.leaf { law := 1209, dual := 2594, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1210, dual := 2631, proof := sorry })
                      (RArray.leaf { law := 1211, dual := 2474, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1212, dual := 2613, proof := sorry })
                      (RArray.leaf { law := 1213, dual := 2607, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1214, dual := 2548, proof := sorry })
                      (RArray.leaf { law := 1215, dual := 2616, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1216, dual := 2491, proof := sorry })
                      (RArray.leaf { law := 1217, dual := 2638, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1218, dual := 2626, proof := sorry })
                      (RArray.leaf { law := 1219, dual := 2599, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1220, dual := 2565, proof := sorry })
                      (RArray.leaf { law := 1221, dual := 2642, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1222, dual := 2237, proof := sorry })
                      (RArray.leaf { law := 1223, dual := 2289, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1224, dual := 2252, proof := sorry })
                      (RArray.leaf { law := 1225, dual := 2326, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1226, dual := 2363, proof := sorry })
                      (RArray.leaf { law := 1227, dual := 2242, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1228, dual := 2299, proof := sorry })
                      (RArray.leaf { law := 1229, dual := 2309, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1230, dual := 2262, proof := sorry })
                      (RArray.leaf { law := 1231, dual := 2336, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1232, dual := 2397, proof := sorry })
                      (RArray.leaf { law := 1233, dual := 2272, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1234, dual := 2380, proof := sorry })
                      (RArray.leaf { law := 1235, dual := 2346, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1236, dual := 2414, proof := sorry })
                      (RArray.leaf { law := 1237, dual := 2239, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1238, dual := 2292, proof := sorry })
                      (RArray.leaf { law := 1239, dual := 2295, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1240, dual := 2255, proof := sorry })
                      (RArray.leaf { law := 1241, dual := 2329, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1242, dual := 2371, proof := sorry })
                      (RArray.leaf { law := 1243, dual := 2258, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1244, dual := 2367, proof := sorry })
                      (RArray.leaf { law := 1245, dual := 2332, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1246, dual := 2375, proof := sorry })
                      (RArray.leaf { law := 1247, dual := 2245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1248, dual := 2302, proof := sorry })
                      (RArray.leaf { law := 1249, dual := 2317, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1250, dual := 2265, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1251, dual := 2339, proof := sorry })
                      (RArray.leaf { law := 1252, dual := 2405, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1253, dual := 2280, proof := sorry })
                      (RArray.leaf { law := 1254, dual := 2384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1255, dual := 2354, proof := sorry })
                      (RArray.leaf { law := 1256, dual := 2429, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1257, dual := 2248, proof := sorry })
                      (RArray.leaf { law := 1258, dual := 2313, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1259, dual := 2305, proof := sorry })
                      (RArray.leaf { law := 1260, dual := 2321, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1261, dual := 2276, proof := sorry })
                      (RArray.leaf { law := 1262, dual := 2350, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1263, dual := 2388, proof := sorry })
                      (RArray.leaf { law := 1264, dual := 2424, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1265, dual := 2268, proof := sorry })
                      (RArray.leaf { law := 1266, dual := 2401, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1267, dual := 2342, proof := sorry })
                      (RArray.leaf { law := 1268, dual := 2409, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1269, dual := 2284, proof := sorry })
                      (RArray.leaf { law := 1270, dual := 2419, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1271, dual := 2392, proof := sorry })
                      (RArray.leaf { law := 1272, dual := 2358, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1273, dual := 2434, proof := sorry })
                      (RArray.leaf { law := 1274, dual := 2238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1275, dual := 2290, proof := sorry })
                      (RArray.leaf { law := 1276, dual := 2291, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1277, dual := 2253, proof := sorry })
                      (RArray.leaf { law := 1278, dual := 2327, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1279, dual := 2365, proof := sorry })
                      (RArray.leaf { law := 1280, dual := 2254, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1281, dual := 2364, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1282, dual := 2328, proof := sorry })
                      (RArray.leaf { law := 1283, dual := 2366, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1284, dual := 2243, proof := sorry })
                      (RArray.leaf { law := 1285, dual := 2300, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1286, dual := 2311, proof := sorry })
                      (RArray.leaf { law := 1287, dual := 2263, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1288, dual := 2337, proof := sorry })
                      (RArray.leaf { law := 1289, dual := 2399, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1290, dual := 2274, proof := sorry })
                      (RArray.leaf { law := 1291, dual := 2381, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1292, dual := 2348, proof := sorry })
                      (RArray.leaf { law := 1293, dual := 2417, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1294, dual := 2244, proof := sorry })
                      (RArray.leaf { law := 1295, dual := 2310, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1296, dual := 2301, proof := sorry })
                      (RArray.leaf { law := 1297, dual := 2312, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1298, dual := 2273, proof := sorry })
                      (RArray.leaf { law := 1299, dual := 2347, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1300, dual := 2382, proof := sorry })
                      (RArray.leaf { law := 1301, dual := 2416, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1302, dual := 2264, proof := sorry })
                      (RArray.leaf { law := 1303, dual := 2398, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1304, dual := 2338, proof := sorry })
                      (RArray.leaf { law := 1305, dual := 2400, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1306, dual := 2275, proof := sorry })
                      (RArray.leaf { law := 1307, dual := 2415, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1308, dual := 2383, proof := sorry })
                      (RArray.leaf { law := 1309, dual := 2349, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1310, dual := 2418, proof := sorry })
                      (RArray.leaf { law := 1311, dual := 2240, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1312, dual := 2293, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1313, dual := 2297, proof := sorry })
                      (RArray.leaf { law := 1314, dual := 2256, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1315, dual := 2330, proof := sorry })
                      (RArray.leaf { law := 1316, dual := 2373, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1317, dual := 2260, proof := sorry })
                      (RArray.leaf { law := 1318, dual := 2368, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1319, dual := 2334, proof := sorry })
                      (RArray.leaf { law := 1320, dual := 2378, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1321, dual := 2246, proof := sorry })
                      (RArray.leaf { law := 1322, dual := 2303, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1323, dual := 2319, proof := sorry })
                      (RArray.leaf { law := 1324, dual := 2266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1325, dual := 2340, proof := sorry })
                      (RArray.leaf { law := 1326, dual := 2407, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1327, dual := 2282, proof := sorry })
                      (RArray.leaf { law := 1328, dual := 2385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1329, dual := 2356, proof := sorry })
                      (RArray.leaf { law := 1330, dual := 2432, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1331, dual := 2250, proof := sorry })
                      (RArray.leaf { law := 1332, dual := 2314, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1333, dual := 2307, proof := sorry })
                      (RArray.leaf { law := 1334, dual := 2324, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1335, dual := 2277, proof := sorry })
                      (RArray.leaf { law := 1336, dual := 2351, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1337, dual := 2390, proof := sorry })
                      (RArray.leaf { law := 1338, dual := 2426, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1339, dual := 2270, proof := sorry })
                      (RArray.leaf { law := 1340, dual := 2402, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1341, dual := 2344, proof := sorry })
                      (RArray.leaf { law := 1342, dual := 2412, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1343, dual := 2287, proof := sorry })
                      (RArray.leaf { law := 1344, dual := 2420, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1345, dual := 2395, proof := sorry })
                      (RArray.leaf { law := 1346, dual := 2361, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1347, dual := 2438, proof := sorry })
                      (RArray.leaf { law := 1348, dual := 2241, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1349, dual := 2296, proof := sorry })
                      (RArray.leaf { law := 1350, dual := 2294, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1351, dual := 2298, proof := sorry })
                      (RArray.leaf { law := 1352, dual := 2259, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1353, dual := 2333, proof := sorry })
                      (RArray.leaf { law := 1354, dual := 2369, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1355, dual := 2377, proof := sorry })
                      (RArray.leaf { law := 1356, dual := 2257, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1357, dual := 2372, proof := sorry })
                      (RArray.leaf { law := 1358, dual := 2331, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1359, dual := 2374, proof := sorry })
                      (RArray.leaf { law := 1360, dual := 2261, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1361, dual := 2376, proof := sorry })
                      (RArray.leaf { law := 1362, dual := 2370, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1363, dual := 2335, proof := sorry })
                      (RArray.leaf { law := 1364, dual := 2379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1365, dual := 2249, proof := sorry })
                      (RArray.leaf { law := 1366, dual := 2306, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1367, dual := 2315, proof := sorry })
                      (RArray.leaf { law := 1368, dual := 2323, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1369, dual := 2269, proof := sorry })
                      (RArray.leaf { law := 1370, dual := 2343, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1371, dual := 2403, proof := sorry })
                      (RArray.leaf { law := 1372, dual := 2411, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1373, dual := 2278, proof := sorry })
                      (RArray.leaf { law := 1374, dual := 2389, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1375, dual := 2352, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1376, dual := 2427, proof := sorry })
                      (RArray.leaf { law := 1377, dual := 2286, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1378, dual := 2393, proof := sorry })
                      (RArray.leaf { law := 1379, dual := 2422, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1380, dual := 2360, proof := sorry })
                      (RArray.leaf { law := 1381, dual := 2437, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1382, dual := 2247, proof := sorry })
                      (RArray.leaf { law := 1383, dual := 2318, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1384, dual := 2304, proof := sorry })
                      (RArray.leaf { law := 1385, dual := 2320, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1386, dual := 2281, proof := sorry })
                      (RArray.leaf { law := 1387, dual := 2355, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1388, dual := 2386, proof := sorry })
                      (RArray.leaf { law := 1389, dual := 2431, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1390, dual := 2267, proof := sorry })
                      (RArray.leaf { law := 1391, dual := 2406, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1392, dual := 2341, proof := sorry })
                      (RArray.leaf { law := 1393, dual := 2408, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1394, dual := 2283, proof := sorry })
                      (RArray.leaf { law := 1395, dual := 2430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1396, dual := 2387, proof := sorry })
                      (RArray.leaf { law := 1397, dual := 2357, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1398, dual := 2433, proof := sorry })
                      (RArray.leaf { law := 1399, dual := 2251, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1400, dual := 2322, proof := sorry })
                      (RArray.leaf { law := 1401, dual := 2316, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1402, dual := 2308, proof := sorry })
                      (RArray.leaf { law := 1403, dual := 2325, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1404, dual := 2285, proof := sorry })
                      (RArray.leaf { law := 1405, dual := 2359, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1406, dual := 2421, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1407, dual := 2394, proof := sorry })
                      (RArray.leaf { law := 1408, dual := 2436, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1409, dual := 2279, proof := sorry })
                      (RArray.leaf { law := 1410, dual := 2425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1411, dual := 2353, proof := sorry })
                      (RArray.leaf { law := 1412, dual := 2391, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1413, dual := 2428, proof := sorry })
                      (RArray.leaf { law := 1414, dual := 2271, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1415, dual := 2410, proof := sorry })
                      (RArray.leaf { law := 1416, dual := 2404, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1417, dual := 2345, proof := sorry })
                      (RArray.leaf { law := 1418, dual := 2413, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1419, dual := 2288, proof := sorry })
                      (RArray.leaf { law := 1420, dual := 2435, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1421, dual := 2423, proof := sorry })
                      (RArray.leaf { law := 1422, dual := 2396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1423, dual := 2362, proof := sorry })
                      (RArray.leaf { law := 1424, dual := 2439, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1425, dual := 2034, proof := sorry })
                      (RArray.leaf { law := 1426, dual := 2086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1427, dual := 2049, proof := sorry })
                      (RArray.leaf { law := 1428, dual := 2123, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1429, dual := 2160, proof := sorry })
                      (RArray.leaf { law := 1430, dual := 2039, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1431, dual := 2096, proof := sorry })
                      (RArray.leaf { law := 1432, dual := 2106, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1433, dual := 2059, proof := sorry })
                      (RArray.leaf { law := 1434, dual := 2133, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1435, dual := 2194, proof := sorry })
                      (RArray.leaf { law := 1436, dual := 2069, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1437, dual := 2177, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1438, dual := 2143, proof := sorry })
                      (RArray.leaf { law := 1439, dual := 2211, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1440, dual := 2036, proof := sorry })
                      (RArray.leaf { law := 1441, dual := 2089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1442, dual := 2092, proof := sorry })
                      (RArray.leaf { law := 1443, dual := 2052, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1444, dual := 2126, proof := sorry })
                      (RArray.leaf { law := 1445, dual := 2168, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1446, dual := 2055, proof := sorry })
                      (RArray.leaf { law := 1447, dual := 2164, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1448, dual := 2129, proof := sorry })
                      (RArray.leaf { law := 1449, dual := 2172, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1450, dual := 2042, proof := sorry })
                      (RArray.leaf { law := 1451, dual := 2099, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1452, dual := 2114, proof := sorry })
                      (RArray.leaf { law := 1453, dual := 2062, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1454, dual := 2136, proof := sorry })
                      (RArray.leaf { law := 1455, dual := 2202, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1456, dual := 2077, proof := sorry })
                      (RArray.leaf { law := 1457, dual := 2181, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1458, dual := 2151, proof := sorry })
                      (RArray.leaf { law := 1459, dual := 2226, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1460, dual := 2045, proof := sorry })
                      (RArray.leaf { law := 1461, dual := 2110, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1462, dual := 2102, proof := sorry })
                      (RArray.leaf { law := 1463, dual := 2118, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1464, dual := 2073, proof := sorry })
                      (RArray.leaf { law := 1465, dual := 2147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1466, dual := 2185, proof := sorry })
                      (RArray.leaf { law := 1467, dual := 2221, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1468, dual := 2065, proof := sorry })
                      (RArray.leaf { law := 1469, dual := 2198, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1470, dual := 2139, proof := sorry })
                      (RArray.leaf { law := 1471, dual := 2206, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1472, dual := 2081, proof := sorry })
                      (RArray.leaf { law := 1473, dual := 2216, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1474, dual := 2189, proof := sorry })
                      (RArray.leaf { law := 1475, dual := 2155, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1476, dual := 2231, proof := sorry })
                      (RArray.leaf { law := 1477, dual := 2035, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1478, dual := 2087, proof := sorry })
                      (RArray.leaf { law := 1479, dual := 2088, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1480, dual := 2050, proof := sorry })
                      (RArray.leaf { law := 1481, dual := 2124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1482, dual := 2162, proof := sorry })
                      (RArray.leaf { law := 1483, dual := 2051, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1484, dual := 2161, proof := sorry })
                      (RArray.leaf { law := 1485, dual := 2125, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1486, dual := 2163, proof := sorry })
                      (RArray.leaf { law := 1487, dual := 2040, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1488, dual := 2097, proof := sorry })
                      (RArray.leaf { law := 1489, dual := 2108, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1490, dual := 2060, proof := sorry })
                      (RArray.leaf { law := 1491, dual := 2134, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1492, dual := 2196, proof := sorry })
                      (RArray.leaf { law := 1493, dual := 2071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1494, dual := 2178, proof := sorry })
                      (RArray.leaf { law := 1495, dual := 2145, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1496, dual := 2214, proof := sorry })
                      (RArray.leaf { law := 1497, dual := 2041, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1498, dual := 2107, proof := sorry })
                      (RArray.leaf { law := 1499, dual := 2098, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1500, dual := 2109, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1501, dual := 2070, proof := sorry })
                      (RArray.leaf { law := 1502, dual := 2144, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1503, dual := 2179, proof := sorry })
                      (RArray.leaf { law := 1504, dual := 2213, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1505, dual := 2061, proof := sorry })
                      (RArray.leaf { law := 1506, dual := 2195, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1507, dual := 2135, proof := sorry })
                      (RArray.leaf { law := 1508, dual := 2197, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1509, dual := 2072, proof := sorry })
                      (RArray.leaf { law := 1510, dual := 2212, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1511, dual := 2180, proof := sorry })
                      (RArray.leaf { law := 1512, dual := 2146, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1513, dual := 2215, proof := sorry })
                      (RArray.leaf { law := 1514, dual := 2037, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1515, dual := 2090, proof := sorry })
                      (RArray.leaf { law := 1516, dual := 2094, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1517, dual := 2053, proof := sorry })
                      (RArray.leaf { law := 1518, dual := 2127, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1519, dual := 2170, proof := sorry })
                      (RArray.leaf { law := 1520, dual := 2057, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1521, dual := 2165, proof := sorry })
                      (RArray.leaf { law := 1522, dual := 2131, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1523, dual := 2175, proof := sorry })
                      (RArray.leaf { law := 1524, dual := 2043, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1525, dual := 2100, proof := sorry })
                      (RArray.leaf { law := 1526, dual := 2116, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1527, dual := 2063, proof := sorry })
                      (RArray.leaf { law := 1528, dual := 2137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1529, dual := 2204, proof := sorry })
                      (RArray.leaf { law := 1530, dual := 2079, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1531, dual := 2182, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1532, dual := 2153, proof := sorry })
                      (RArray.leaf { law := 1533, dual := 2229, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1534, dual := 2047, proof := sorry })
                      (RArray.leaf { law := 1535, dual := 2111, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1536, dual := 2104, proof := sorry })
                      (RArray.leaf { law := 1537, dual := 2121, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1538, dual := 2074, proof := sorry })
                      (RArray.leaf { law := 1539, dual := 2148, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1540, dual := 2187, proof := sorry })
                      (RArray.leaf { law := 1541, dual := 2223, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1542, dual := 2067, proof := sorry })
                      (RArray.leaf { law := 1543, dual := 2199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1544, dual := 2141, proof := sorry })
                      (RArray.leaf { law := 1545, dual := 2209, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1546, dual := 2084, proof := sorry })
                      (RArray.leaf { law := 1547, dual := 2217, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1548, dual := 2192, proof := sorry })
                      (RArray.leaf { law := 1549, dual := 2158, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1550, dual := 2235, proof := sorry })
                      (RArray.leaf { law := 1551, dual := 2038, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1552, dual := 2093, proof := sorry })
                      (RArray.leaf { law := 1553, dual := 2091, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1554, dual := 2095, proof := sorry })
                      (RArray.leaf { law := 1555, dual := 2056, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1556, dual := 2130, proof := sorry })
                      (RArray.leaf { law := 1557, dual := 2166, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1558, dual := 2174, proof := sorry })
                      (RArray.leaf { law := 1559, dual := 2054, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1560, dual := 2169, proof := sorry })
                      (RArray.leaf { law := 1561, dual := 2128, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1562, dual := 2171, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1563, dual := 2058, proof := sorry })
                      (RArray.leaf { law := 1564, dual := 2173, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1565, dual := 2167, proof := sorry })
                      (RArray.leaf { law := 1566, dual := 2132, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1567, dual := 2176, proof := sorry })
                      (RArray.leaf { law := 1568, dual := 2046, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1569, dual := 2103, proof := sorry })
                      (RArray.leaf { law := 1570, dual := 2112, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1571, dual := 2120, proof := sorry })
                      (RArray.leaf { law := 1572, dual := 2066, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1573, dual := 2140, proof := sorry })
                      (RArray.leaf { law := 1574, dual := 2200, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1575, dual := 2208, proof := sorry })
                      (RArray.leaf { law := 1576, dual := 2075, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1577, dual := 2186, proof := sorry })
                      (RArray.leaf { law := 1578, dual := 2149, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1579, dual := 2224, proof := sorry })
                      (RArray.leaf { law := 1580, dual := 2083, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1581, dual := 2190, proof := sorry })
                      (RArray.leaf { law := 1582, dual := 2219, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1583, dual := 2157, proof := sorry })
                      (RArray.leaf { law := 1584, dual := 2234, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1585, dual := 2044, proof := sorry })
                      (RArray.leaf { law := 1586, dual := 2115, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1587, dual := 2101, proof := sorry })
                      (RArray.leaf { law := 1588, dual := 2117, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1589, dual := 2078, proof := sorry })
                      (RArray.leaf { law := 1590, dual := 2152, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1591, dual := 2183, proof := sorry })
                      (RArray.leaf { law := 1592, dual := 2228, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1593, dual := 2064, proof := sorry })
                      (RArray.leaf { law := 1594, dual := 2203, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1595, dual := 2138, proof := sorry })
                      (RArray.leaf { law := 1596, dual := 2205, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1597, dual := 2080, proof := sorry })
                      (RArray.leaf { law := 1598, dual := 2227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1599, dual := 2184, proof := sorry })
                      (RArray.leaf { law := 1600, dual := 2154, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1601, dual := 2230, proof := sorry })
                      (RArray.leaf { law := 1602, dual := 2048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1603, dual := 2119, proof := sorry })
                      (RArray.leaf { law := 1604, dual := 2113, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1605, dual := 2105, proof := sorry })
                      (RArray.leaf { law := 1606, dual := 2122, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1607, dual := 2082, proof := sorry })
                      (RArray.leaf { law := 1608, dual := 2156, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1609, dual := 2218, proof := sorry })
                      (RArray.leaf { law := 1610, dual := 2191, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1611, dual := 2233, proof := sorry })
                      (RArray.leaf { law := 1612, dual := 2076, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1613, dual := 2222, proof := sorry })
                      (RArray.leaf { law := 1614, dual := 2150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1615, dual := 2188, proof := sorry })
                      (RArray.leaf { law := 1616, dual := 2225, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1617, dual := 2068, proof := sorry })
                      (RArray.leaf { law := 1618, dual := 2207, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1619, dual := 2201, proof := sorry })
                      (RArray.leaf { law := 1620, dual := 2142, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1621, dual := 2210, proof := sorry })
                      (RArray.leaf { law := 1622, dual := 2085, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1623, dual := 2232, proof := sorry })
                      (RArray.leaf { law := 1624, dual := 2220, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1625, dual := 2193, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1626, dual := 2159, proof := sorry })
                      (RArray.leaf { law := 1627, dual := 2236, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1628, dual := 1831, proof := sorry })
                      (RArray.leaf { law := 1629, dual := 1883, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1630, dual := 1846, proof := sorry })
                      (RArray.leaf { law := 1631, dual := 1920, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1632, dual := 1957, proof := sorry })
                      (RArray.leaf { law := 1633, dual := 1836, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1634, dual := 1893, proof := sorry })
                      (RArray.leaf { law := 1635, dual := 1903, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1636, dual := 1856, proof := sorry })
                      (RArray.leaf { law := 1637, dual := 1930, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1638, dual := 1991, proof := sorry })
                      (RArray.leaf { law := 1639, dual := 1866, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1640, dual := 1974, proof := sorry })
                      (RArray.leaf { law := 1641, dual := 1940, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1642, dual := 2008, proof := sorry })
                      (RArray.leaf { law := 1643, dual := 1833, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1644, dual := 1886, proof := sorry })
                      (RArray.leaf { law := 1645, dual := 1889, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1646, dual := 1849, proof := sorry })
                      (RArray.leaf { law := 1647, dual := 1923, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1648, dual := 1965, proof := sorry })
                      (RArray.leaf { law := 1649, dual := 1852, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1650, dual := 1961, proof := sorry })
                      (RArray.leaf { law := 1651, dual := 1926, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1652, dual := 1969, proof := sorry })
                      (RArray.leaf { law := 1653, dual := 1839, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1654, dual := 1896, proof := sorry })
                      (RArray.leaf { law := 1655, dual := 1911, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1656, dual := 1859, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1657, dual := 1933, proof := sorry })
                      (RArray.leaf { law := 1658, dual := 1999, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1659, dual := 1874, proof := sorry })
                      (RArray.leaf { law := 1660, dual := 1978, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1661, dual := 1948, proof := sorry })
                      (RArray.leaf { law := 1662, dual := 2023, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1663, dual := 1842, proof := sorry })
                      (RArray.leaf { law := 1664, dual := 1907, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1665, dual := 1899, proof := sorry })
                      (RArray.leaf { law := 1666, dual := 1915, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1667, dual := 1870, proof := sorry })
                      (RArray.leaf { law := 1668, dual := 1944, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1669, dual := 1982, proof := sorry })
                      (RArray.leaf { law := 1670, dual := 2018, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1671, dual := 1862, proof := sorry })
                      (RArray.leaf { law := 1672, dual := 1995, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1673, dual := 1936, proof := sorry })
                      (RArray.leaf { law := 1674, dual := 2003, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1675, dual := 1878, proof := sorry })
                      (RArray.leaf { law := 1676, dual := 2013, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1677, dual := 1986, proof := sorry })
                      (RArray.leaf { law := 1678, dual := 1952, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1679, dual := 2028, proof := sorry })
                      (RArray.leaf { law := 1680, dual := 1832, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1681, dual := 1884, proof := sorry })
                      (RArray.leaf { law := 1682, dual := 1885, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1683, dual := 1847, proof := sorry })
                      (RArray.leaf { law := 1684, dual := 1921, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1685, dual := 1959, proof := sorry })
                      (RArray.leaf { law := 1686, dual := 1848, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1687, dual := 1958, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1688, dual := 1922, proof := sorry })
                      (RArray.leaf { law := 1689, dual := 1960, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1690, dual := 1837, proof := sorry })
                      (RArray.leaf { law := 1691, dual := 1894, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1692, dual := 1905, proof := sorry })
                      (RArray.leaf { law := 1693, dual := 1857, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1694, dual := 1931, proof := sorry })
                      (RArray.leaf { law := 1695, dual := 1993, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1696, dual := 1868, proof := sorry })
                      (RArray.leaf { law := 1697, dual := 1975, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1698, dual := 1942, proof := sorry })
                      (RArray.leaf { law := 1699, dual := 2011, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1700, dual := 1838, proof := sorry })
                      (RArray.leaf { law := 1701, dual := 1904, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1702, dual := 1895, proof := sorry })
                      (RArray.leaf { law := 1703, dual := 1906, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1704, dual := 1867, proof := sorry })
                      (RArray.leaf { law := 1705, dual := 1941, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1706, dual := 1976, proof := sorry })
                      (RArray.leaf { law := 1707, dual := 2010, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1708, dual := 1858, proof := sorry })
                      (RArray.leaf { law := 1709, dual := 1992, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1710, dual := 1932, proof := sorry })
                      (RArray.leaf { law := 1711, dual := 1994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1712, dual := 1869, proof := sorry })
                      (RArray.leaf { law := 1713, dual := 2009, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1714, dual := 1977, proof := sorry })
                      (RArray.leaf { law := 1715, dual := 1943, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1716, dual := 2012, proof := sorry })
                      (RArray.leaf { law := 1717, dual := 1834, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1718, dual := 1887, proof := sorry })
                      (RArray.leaf { law := 1719, dual := 1891, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1720, dual := 1850, proof := sorry })
                      (RArray.leaf { law := 1721, dual := 1924, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1722, dual := 1967, proof := sorry })
                      (RArray.leaf { law := 1723, dual := 1854, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1724, dual := 1962, proof := sorry })
                      (RArray.leaf { law := 1725, dual := 1928, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1726, dual := 1972, proof := sorry })
                      (RArray.leaf { law := 1727, dual := 1840, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1728, dual := 1897, proof := sorry })
                      (RArray.leaf { law := 1729, dual := 1913, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1730, dual := 1860, proof := sorry })
                      (RArray.leaf { law := 1731, dual := 1934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1732, dual := 2001, proof := sorry })
                      (RArray.leaf { law := 1733, dual := 1876, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1734, dual := 1979, proof := sorry })
                      (RArray.leaf { law := 1735, dual := 1950, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1736, dual := 2026, proof := sorry })
                      (RArray.leaf { law := 1737, dual := 1844, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1738, dual := 1908, proof := sorry })
                      (RArray.leaf { law := 1739, dual := 1901, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1740, dual := 1918, proof := sorry })
                      (RArray.leaf { law := 1741, dual := 1871, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1742, dual := 1945, proof := sorry })
                      (RArray.leaf { law := 1743, dual := 1984, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1744, dual := 2020, proof := sorry })
                      (RArray.leaf { law := 1745, dual := 1864, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1746, dual := 1996, proof := sorry })
                      (RArray.leaf { law := 1747, dual := 1938, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1748, dual := 2006, proof := sorry })
                      (RArray.leaf { law := 1749, dual := 1881, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1750, dual := 2014, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1751, dual := 1989, proof := sorry })
                      (RArray.leaf { law := 1752, dual := 1955, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1753, dual := 2032, proof := sorry })
                      (RArray.leaf { law := 1754, dual := 1835, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1755, dual := 1890, proof := sorry })
                      (RArray.leaf { law := 1756, dual := 1888, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1757, dual := 1892, proof := sorry })
                      (RArray.leaf { law := 1758, dual := 1853, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1759, dual := 1927, proof := sorry })
                      (RArray.leaf { law := 1760, dual := 1963, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1761, dual := 1971, proof := sorry })
                      (RArray.leaf { law := 1762, dual := 1851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1763, dual := 1966, proof := sorry })
                      (RArray.leaf { law := 1764, dual := 1925, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1765, dual := 1968, proof := sorry })
                      (RArray.leaf { law := 1766, dual := 1855, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1767, dual := 1970, proof := sorry })
                      (RArray.leaf { law := 1768, dual := 1964, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1769, dual := 1929, proof := sorry })
                      (RArray.leaf { law := 1770, dual := 1973, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1771, dual := 1843, proof := sorry })
                      (RArray.leaf { law := 1772, dual := 1900, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1773, dual := 1909, proof := sorry })
                      (RArray.leaf { law := 1774, dual := 1917, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1775, dual := 1863, proof := sorry })
                      (RArray.leaf { law := 1776, dual := 1937, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1777, dual := 1997, proof := sorry })
                      (RArray.leaf { law := 1778, dual := 2005, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1779, dual := 1872, proof := sorry })
                      (RArray.leaf { law := 1780, dual := 1983, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1781, dual := 1946, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1782, dual := 2021, proof := sorry })
                      (RArray.leaf { law := 1783, dual := 1880, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1784, dual := 1987, proof := sorry })
                      (RArray.leaf { law := 1785, dual := 2016, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1786, dual := 1954, proof := sorry })
                      (RArray.leaf { law := 1787, dual := 2031, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1788, dual := 1841, proof := sorry })
                      (RArray.leaf { law := 1789, dual := 1912, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1790, dual := 1898, proof := sorry })
                      (RArray.leaf { law := 1791, dual := 1914, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1792, dual := 1875, proof := sorry })
                      (RArray.leaf { law := 1793, dual := 1949, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1794, dual := 1980, proof := sorry })
                      (RArray.leaf { law := 1795, dual := 2025, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1796, dual := 1861, proof := sorry })
                      (RArray.leaf { law := 1797, dual := 2000, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1798, dual := 1935, proof := sorry })
                      (RArray.leaf { law := 1799, dual := 2002, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1800, dual := 1877, proof := sorry })
                      (RArray.leaf { law := 1801, dual := 2024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1802, dual := 1981, proof := sorry })
                      (RArray.leaf { law := 1803, dual := 1951, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1804, dual := 2027, proof := sorry })
                      (RArray.leaf { law := 1805, dual := 1845, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1806, dual := 1916, proof := sorry })
                      (RArray.leaf { law := 1807, dual := 1910, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1808, dual := 1902, proof := sorry })
                      (RArray.leaf { law := 1809, dual := 1919, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1810, dual := 1879, proof := sorry })
                      (RArray.leaf { law := 1811, dual := 1953, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1812, dual := 2015, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1813, dual := 1988, proof := sorry })
                      (RArray.leaf { law := 1814, dual := 2030, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1815, dual := 1873, proof := sorry })
                      (RArray.leaf { law := 1816, dual := 2019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1817, dual := 1947, proof := sorry })
                      (RArray.leaf { law := 1818, dual := 1985, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1819, dual := 2022, proof := sorry })
                      (RArray.leaf { law := 1820, dual := 1865, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1821, dual := 2004, proof := sorry })
                      (RArray.leaf { law := 1822, dual := 1998, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1823, dual := 1939, proof := sorry })
                      (RArray.leaf { law := 1824, dual := 2007, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1825, dual := 1882, proof := sorry })
                      (RArray.leaf { law := 1826, dual := 2029, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1827, dual := 2017, proof := sorry })
                      (RArray.leaf { law := 1828, dual := 1990, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1829, dual := 1956, proof := sorry })
                      (RArray.leaf { law := 1830, dual := 2033, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1831, dual := 1628, proof := sorry })
                      (RArray.leaf { law := 1832, dual := 1680, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1833, dual := 1643, proof := sorry })
                      (RArray.leaf { law := 1834, dual := 1717, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1835, dual := 1754, proof := sorry })
                      (RArray.leaf { law := 1836, dual := 1633, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1837, dual := 1690, proof := sorry })
                      (RArray.leaf { law := 1838, dual := 1700, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1839, dual := 1653, proof := sorry })
                      (RArray.leaf { law := 1840, dual := 1727, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1841, dual := 1788, proof := sorry })
                      (RArray.leaf { law := 1842, dual := 1663, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1843, dual := 1771, proof := sorry })
                      (RArray.leaf { law := 1844, dual := 1737, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1845, dual := 1805, proof := sorry })
                      (RArray.leaf { law := 1846, dual := 1630, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1847, dual := 1683, proof := sorry })
                      (RArray.leaf { law := 1848, dual := 1686, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1849, dual := 1646, proof := sorry })
                      (RArray.leaf { law := 1850, dual := 1720, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1851, dual := 1762, proof := sorry })
                      (RArray.leaf { law := 1852, dual := 1649, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1853, dual := 1758, proof := sorry })
                      (RArray.leaf { law := 1854, dual := 1723, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1855, dual := 1766, proof := sorry })
                      (RArray.leaf { law := 1856, dual := 1636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1857, dual := 1693, proof := sorry })
                      (RArray.leaf { law := 1858, dual := 1708, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1859, dual := 1656, proof := sorry })
                      (RArray.leaf { law := 1860, dual := 1730, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1861, dual := 1796, proof := sorry })
                      (RArray.leaf { law := 1862, dual := 1671, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1863, dual := 1775, proof := sorry })
                      (RArray.leaf { law := 1864, dual := 1745, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1865, dual := 1820, proof := sorry })
                      (RArray.leaf { law := 1866, dual := 1639, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1867, dual := 1704, proof := sorry })
                      (RArray.leaf { law := 1868, dual := 1696, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1869, dual := 1712, proof := sorry })
                      (RArray.leaf { law := 1870, dual := 1667, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1871, dual := 1741, proof := sorry })
                      (RArray.leaf { law := 1872, dual := 1779, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1873, dual := 1815, proof := sorry })
                      (RArray.leaf { law := 1874, dual := 1659, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1875, dual := 1792, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1876, dual := 1733, proof := sorry })
                      (RArray.leaf { law := 1877, dual := 1800, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1878, dual := 1675, proof := sorry })
                      (RArray.leaf { law := 1879, dual := 1810, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1880, dual := 1783, proof := sorry })
                      (RArray.leaf { law := 1881, dual := 1749, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1882, dual := 1825, proof := sorry })
                      (RArray.leaf { law := 1883, dual := 1629, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1884, dual := 1681, proof := sorry })
                      (RArray.leaf { law := 1885, dual := 1682, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1886, dual := 1644, proof := sorry })
                      (RArray.leaf { law := 1887, dual := 1718, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1888, dual := 1756, proof := sorry })
                      (RArray.leaf { law := 1889, dual := 1645, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1890, dual := 1755, proof := sorry })
                      (RArray.leaf { law := 1891, dual := 1719, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1892, dual := 1757, proof := sorry })
                      (RArray.leaf { law := 1893, dual := 1634, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1894, dual := 1691, proof := sorry })
                      (RArray.leaf { law := 1895, dual := 1702, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1896, dual := 1654, proof := sorry })
                      (RArray.leaf { law := 1897, dual := 1728, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1898, dual := 1790, proof := sorry })
                      (RArray.leaf { law := 1899, dual := 1665, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1900, dual := 1772, proof := sorry })
                      (RArray.leaf { law := 1901, dual := 1739, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1902, dual := 1808, proof := sorry })
                      (RArray.leaf { law := 1903, dual := 1635, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1904, dual := 1701, proof := sorry })
                      (RArray.leaf { law := 1905, dual := 1692, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1906, dual := 1703, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1907, dual := 1664, proof := sorry })
                      (RArray.leaf { law := 1908, dual := 1738, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1909, dual := 1773, proof := sorry })
                      (RArray.leaf { law := 1910, dual := 1807, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1911, dual := 1655, proof := sorry })
                      (RArray.leaf { law := 1912, dual := 1789, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1913, dual := 1729, proof := sorry })
                      (RArray.leaf { law := 1914, dual := 1791, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1915, dual := 1666, proof := sorry })
                      (RArray.leaf { law := 1916, dual := 1806, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1917, dual := 1774, proof := sorry })
                      (RArray.leaf { law := 1918, dual := 1740, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1919, dual := 1809, proof := sorry })
                      (RArray.leaf { law := 1920, dual := 1631, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1921, dual := 1684, proof := sorry })
                      (RArray.leaf { law := 1922, dual := 1688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1923, dual := 1647, proof := sorry })
                      (RArray.leaf { law := 1924, dual := 1721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1925, dual := 1764, proof := sorry })
                      (RArray.leaf { law := 1926, dual := 1651, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1927, dual := 1759, proof := sorry })
                      (RArray.leaf { law := 1928, dual := 1725, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1929, dual := 1769, proof := sorry })
                      (RArray.leaf { law := 1930, dual := 1637, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1931, dual := 1694, proof := sorry })
                      (RArray.leaf { law := 1932, dual := 1710, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1933, dual := 1657, proof := sorry })
                      (RArray.leaf { law := 1934, dual := 1731, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1935, dual := 1798, proof := sorry })
                      (RArray.leaf { law := 1936, dual := 1673, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 1937, dual := 1776, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 1938, dual := 1747, proof := sorry })
                      (RArray.leaf { law := 1939, dual := 1823, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1940, dual := 1641, proof := sorry })
                      (RArray.leaf { law := 1941, dual := 1705, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1942, dual := 1698, proof := sorry })
                      (RArray.leaf { law := 1943, dual := 1715, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1944, dual := 1668, proof := sorry })
                      (RArray.leaf { law := 1945, dual := 1742, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1946, dual := 1781, proof := sorry })
                      (RArray.leaf { law := 1947, dual := 1817, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1948, dual := 1661, proof := sorry })
                      (RArray.leaf { law := 1949, dual := 1793, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1950, dual := 1735, proof := sorry })
                      (RArray.leaf { law := 1951, dual := 1803, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1952, dual := 1678, proof := sorry })
                      (RArray.leaf { law := 1953, dual := 1811, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1954, dual := 1786, proof := sorry })
                      (RArray.leaf { law := 1955, dual := 1752, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1956, dual := 1829, proof := sorry })
                      (RArray.leaf { law := 1957, dual := 1632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1958, dual := 1687, proof := sorry })
                      (RArray.leaf { law := 1959, dual := 1685, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1960, dual := 1689, proof := sorry })
                      (RArray.leaf { law := 1961, dual := 1650, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1962, dual := 1724, proof := sorry })
                      (RArray.leaf { law := 1963, dual := 1760, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1964, dual := 1768, proof := sorry })
                      (RArray.leaf { law := 1965, dual := 1648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1966, dual := 1763, proof := sorry })
                      (RArray.leaf { law := 1967, dual := 1722, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1968, dual := 1765, proof := sorry })
                      (RArray.leaf { law := 1969, dual := 1652, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1970, dual := 1767, proof := sorry })
                      (RArray.leaf { law := 1971, dual := 1761, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1972, dual := 1726, proof := sorry })
                      (RArray.leaf { law := 1973, dual := 1770, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1974, dual := 1640, proof := sorry })
                      (RArray.leaf { law := 1975, dual := 1697, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1976, dual := 1706, proof := sorry })
                      (RArray.leaf { law := 1977, dual := 1714, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1978, dual := 1660, proof := sorry })
                      (RArray.leaf { law := 1979, dual := 1734, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1980, dual := 1794, proof := sorry })
                      (RArray.leaf { law := 1981, dual := 1802, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1982, dual := 1669, proof := sorry })
                      (RArray.leaf { law := 1983, dual := 1780, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1984, dual := 1743, proof := sorry })
                      (RArray.leaf { law := 1985, dual := 1818, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1986, dual := 1677, proof := sorry })
                      (RArray.leaf { law := 1987, dual := 1784, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1988, dual := 1813, proof := sorry })
                      (RArray.leaf { law := 1989, dual := 1751, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1990, dual := 1828, proof := sorry })
                      (RArray.leaf { law := 1991, dual := 1638, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1992, dual := 1709, proof := sorry })
                      (RArray.leaf { law := 1993, dual := 1695, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1994, dual := 1711, proof := sorry })
                      (RArray.leaf { law := 1995, dual := 1672, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 1996, dual := 1746, proof := sorry })
                      (RArray.leaf { law := 1997, dual := 1777, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 1998, dual := 1822, proof := sorry })
                      (RArray.leaf { law := 1999, dual := 1658, proof := sorry })))))))))))

end EndToEnd
