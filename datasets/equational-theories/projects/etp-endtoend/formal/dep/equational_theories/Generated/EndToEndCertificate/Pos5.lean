import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Basic.Logic.Basic
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
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.FreeSemigroup
import dep.equational_theories.Generated.MagmaEgg.small._004
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray
import dep.equational_theories.Subgraph

namespace EndToEnd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def _root_.EndToEnd.pos5 : RArray EndToEnd.PosFact :=
RArray.branch 333
  (RArray.branch 166
    (RArray.branch 83
      (RArray.branch 41
        (RArray.branch 20
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 625, conc := 619, proof := sorry })
                  (RArray.leaf { hyp := 627, conc := 617, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 627, conc := 620, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 627, conc := 625, proof := sorry })
                    (RArray.leaf { hyp := 627, conc := 626, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 628, conc := 613, proof := sorry })
                  (RArray.leaf { hyp := 629, conc := 613, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 631, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 632, conc := 613, proof := sorry })
                    (RArray.leaf { hyp := 633, conc := 632, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 634, conc := 615, proof := sorry })
                  (RArray.leaf { hyp := 634, conc := 631, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 637, conc := 630, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 637, conc := 633, proof := sorry })
                    (RArray.leaf { hyp := 637, conc := 636, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 638, conc := 613, proof := sorry })
                  (RArray.leaf { hyp := 62, conc := 46, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 639, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 641, conc := 613, proof := sorry })
                    (RArray.leaf { hyp := 642, conc := 613, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 644, conc := 615, proof := sorry })
                  (RArray.leaf { hyp := 644, conc := 638, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 644, conc := 641, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 645, conc := 615, proof := sorry })
                    (RArray.leaf { hyp := 645, conc := 639, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 645, conc := 642, proof := sorry })
                  (RArray.leaf { hyp := 646, conc := 616, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 646, conc := 638, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 646, conc := 642, proof := sorry })
                    (RArray.leaf { hyp := 647, conc := 640, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 647, conc := 643, proof := sorry })
                  (RArray.leaf { hyp := 651, conc := 630, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 651, conc := 650, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 652, conc := 618, proof := sorry })
                    (RArray.leaf { hyp := 652, conc := 631, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 652, conc := 641, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 654, conc := 619, proof := sorry })
                    (RArray.leaf { hyp := 654, conc := 631, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 655, conc := 653, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 656, conc := 621, proof := sorry })
                    (RArray.leaf { hyp := 656, conc := 628, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 656, conc := 641, proof := sorry })
                  (RArray.leaf { hyp := 657, conc := 621, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 657, conc := 629, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 657, conc := 642, proof := sorry })
                    (RArray.leaf { hyp := 64, conc := 46, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 659, conc := 630, proof := sorry })
                  (RArray.leaf { hyp := 659, conc := 658, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 660, conc := 634, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 660, conc := 644, proof := sorry })
                    (RArray.leaf { hyp := 660, conc := 648, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 660, conc := 652, proof := sorry })
                  (RArray.leaf { hyp := 660, conc := 656, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 661, conc := 653, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 662, conc := 645, proof := sorry })
                    (RArray.leaf { hyp := 662, conc := 650, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 662, conc := 654, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 663, conc := 646, proof := sorry })
                    (RArray.leaf { hyp := 663, conc := 648, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 663, conc := 653, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 664, conc := 637, proof := sorry })
                    (RArray.leaf { hyp := 664, conc := 647, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 664, conc := 651, proof := sorry })
                  (RArray.leaf { hyp := 664, conc := 655, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 664, conc := 659, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 664, conc := 662, proof := sorry })
                    (RArray.leaf { hyp := 664, conc := 663, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 666, conc := 613, proof := sorry })
                  (RArray.leaf { hyp := 668, conc := 613, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 669, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 674, conc := 667, proof := sorry })
                    (RArray.leaf { hyp := 675, conc := 613, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 676, conc := 613, proof := sorry })
                  (RArray.leaf { hyp := 678, conc := 613, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 679, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 683, conc := 675, proof := sorry })
                    (RArray.leaf { hyp := 684, conc := 682, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 685, conc := 665, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 688, conc := 667, proof := sorry })
                    (RArray.leaf { hyp := 688, conc := 677, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 688, conc := 686, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 688, conc := 687, proof := sorry })
                    (RArray.leaf { hyp := 67, conc := 61, proof := sorry }))))))))
      (RArray.branch 41
        (RArray.branch 20
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 689, conc := 618, proof := sorry })
                  (RArray.leaf { hyp := 689, conc := 668, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 689, conc := 678, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 691, conc := 619, proof := sorry })
                    (RArray.leaf { hyp := 692, conc := 680, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 692, conc := 690, proof := sorry })
                  (RArray.leaf { hyp := 693, conc := 665, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 694, conc := 621, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 694, conc := 666, proof := sorry })
                    (RArray.leaf { hyp := 696, conc := 667, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 696, conc := 695, proof := sorry })
                  (RArray.leaf { hyp := 697, conc := 681, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 698, conc := 672, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 698, conc := 682, proof := sorry })
                    (RArray.leaf { hyp := 699, conc := 682, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 700, conc := 690, proof := sorry })
                  (RArray.leaf { hyp := 701, conc := 696, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 701, conc := 699, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 701, conc := 700, proof := sorry })
                    (RArray.leaf { hyp := 702, conc := 613, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 703, conc := 613, proof := sorry })
                  (RArray.leaf { hyp := 705, conc := 613, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 706, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 710, conc := 616, proof := sorry })
                    (RArray.leaf { hyp := 710, conc := 702, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 711, conc := 707, proof := sorry })
                  (RArray.leaf { hyp := 711, conc := 709, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 712, conc := 613, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 715, conc := 613, proof := sorry })
                    (RArray.leaf { hyp := 717, conc := 716, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 70, conc := 50, proof := sorry })
                  (RArray.leaf { hyp := 721, conc := 714, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 721, conc := 717, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 721, conc := 720, proof := sorry })
                    (RArray.leaf { hyp := 722, conc := 618, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 722, conc := 712, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 724, conc := 713, proof := sorry })
                    (RArray.leaf { hyp := 725, conc := 723, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 726, conc := 705, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 729, conc := 707, proof := sorry })
                    (RArray.leaf { hyp := 729, conc := 727, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 729, conc := 728, proof := sorry })
                  (RArray.leaf { hyp := 730, conc := 621, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 730, conc := 702, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 730, conc := 715, proof := sorry })
                    (RArray.leaf { hyp := 731, conc := 703, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 732, conc := 716, proof := sorry })
                  (RArray.leaf { hyp := 733, conc := 731, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 733, conc := 732, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 734, conc := 708, proof := sorry })
                    (RArray.leaf { hyp := 734, conc := 718, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 735, conc := 731, proof := sorry })
                  (RArray.leaf { hyp := 737, conc := 732, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 738, conc := 711, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 738, conc := 721, proof := sorry })
                    (RArray.leaf { hyp := 738, conc := 736, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 72, conc := 46, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 739, conc := 665, proof := sorry })
                    (RArray.leaf { hyp := 742, conc := 741, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 745, conc := 629, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 745, conc := 668, proof := sorry })
                    (RArray.leaf { hyp := 746, conc := 670, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 746, conc := 707, proof := sorry })
                  (RArray.leaf { hyp := 746, conc := 744, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 748, conc := 631, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 73, conc := 47, proof := sorry })
                    (RArray.leaf { hyp := 751, conc := 671, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 752, conc := 744, proof := sorry })
                  (RArray.leaf { hyp := 753, conc := 749, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 754, conc := 673, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 755, conc := 742, proof := sorry })
                    (RArray.leaf { hyp := 74, conc := 46, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 759, conc := 677, proof := sorry })
                  (RArray.leaf { hyp := 763, conc := 761, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 763, conc := 762, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 764, conc := 631, proof := sorry })
                    (RArray.leaf { hyp := 764, conc := 675, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 765, conc := 676, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 767, conc := 677, proof := sorry })
                    (RArray.leaf { hyp := 767, conc := 765, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 767, conc := 766, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 768, conc := 756, proof := sorry })
                    (RArray.leaf { hyp := 768, conc := 764, proof := sorry })))))))))
    (RArray.branch 83
      (RArray.branch 41
        (RArray.branch 20
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 769, conc := 682, proof := sorry })
                  (RArray.leaf { hyp := 772, conc := 759, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 772, conc := 763, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 772, conc := 767, proof := sorry })
                    (RArray.leaf { hyp := 772, conc := 769, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 772, conc := 770, proof := sorry })
                  (RArray.leaf { hyp := 772, conc := 771, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 774, conc := 638, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 774, conc := 666, proof := sorry })
                    (RArray.leaf { hyp := 774, conc := 713, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 775, conc := 713, proof := sorry })
                  (RArray.leaf { hyp := 776, conc := 667, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 777, conc := 638, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 777, conc := 668, proof := sorry })
                    (RArray.leaf { hyp := 778, conc := 669, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 780, conc := 779, proof := sorry })
                  (RArray.leaf { hyp := 784, conc := 782, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 785, conc := 773, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 786, conc := 778, proof := sorry })
                    (RArray.leaf { hyp := 788, conc := 720, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 788, conc := 778, proof := sorry })
                  (RArray.leaf { hyp := 788, conc := 783, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 789, conc := 776, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 789, conc := 786, proof := sorry })
                    (RArray.leaf { hyp := 790, conc := 756, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 790, conc := 773, proof := sorry })
                  (RArray.leaf { hyp := 792, conc := 741, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 793, conc := 775, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 794, conc := 725, proof := sorry })
                    (RArray.leaf { hyp := 794, conc := 742, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 794, conc := 792, proof := sorry })
                  (RArray.leaf { hyp := 795, conc := 648, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 795, conc := 689, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 795, conc := 726, proof := sorry })
                    (RArray.leaf { hyp := 795, conc := 743, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 796, conc := 690, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 799, conc := 729, proof := sorry })
                    (RArray.leaf { hyp := 799, conc := 796, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 799, conc := 797, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 799, conc := 798, proof := sorry })
                    (RArray.leaf { hyp := 800, conc := 747, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 804, conc := 801, proof := sorry })
                  (RArray.leaf { hyp := 804, conc := 802, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 804, conc := 803, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 805, conc := 739, proof := sorry })
                    (RArray.leaf { hyp := 809, conc := 733, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 809, conc := 806, proof := sorry })
                  (RArray.leaf { hyp := 809, conc := 807, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 809, conc := 808, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 810, conc := 660, proof := sorry })
                    (RArray.leaf { hyp := 810, conc := 697, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 810, conc := 751, proof := sorry })
                  (RArray.leaf { hyp := 810, conc := 768, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 810, conc := 785, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 810, conc := 795, proof := sorry })
                    (RArray.leaf { hyp := 811, conc := 735, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 811, conc := 752, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 812, conc := 753, proof := sorry })
                    (RArray.leaf { hyp := 813, conc := 736, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 814, conc := 737, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 815, conc := 789, proof := sorry })
                    (RArray.leaf { hyp := 815, conc := 794, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 815, conc := 799, proof := sorry })
                  (RArray.leaf { hyp := 815, conc := 804, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 815, conc := 809, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 815, conc := 811, proof := sorry })
                    (RArray.leaf { hyp := 815, conc := 812, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 815, conc := 813, proof := sorry })
                  (RArray.leaf { hyp := 815, conc := 814, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 817, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 818, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 80, conc := 73, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 819, conc := 816, proof := sorry })
                  (RArray.leaf { hyp := 820, conc := 817, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 820, conc := 818, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 820, conc := 819, proof := sorry })
                    (RArray.leaf { hyp := 821, conc := 816, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 822, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 823, conc := 821, proof := sorry })
                    (RArray.leaf { hyp := 824, conc := 816, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 825, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 826, conc := 824, proof := sorry })
                    (RArray.leaf { hyp := 827, conc := 818, proof := sorry }))))))))
      (RArray.branch 42
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 827, conc := 821, proof := sorry })
                  (RArray.leaf { hyp := 827, conc := 824, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 81, conc := 61, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 830, conc := 823, proof := sorry })
                    (RArray.leaf { hyp := 830, conc := 827, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 830, conc := 828, proof := sorry })
                  (RArray.leaf { hyp := 830, conc := 829, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 831, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 832, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 833, conc := 817, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 833, conc := 831, proof := sorry })
                  (RArray.leaf { hyp := 833, conc := 832, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 834, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 835, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 836, conc := 817, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 836, conc := 834, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 836, conc := 835, proof := sorry })
                    (RArray.leaf { hyp := 837, conc := 818, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 837, conc := 831, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 837, conc := 834, proof := sorry })
                    (RArray.leaf { hyp := 838, conc := 818, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 838, conc := 832, proof := sorry })
                  (RArray.leaf { hyp := 838, conc := 835, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 839, conc := 819, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 839, conc := 831, proof := sorry })
                    (RArray.leaf { hyp := 839, conc := 835, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 840, conc := 837, proof := sorry })
                  (RArray.leaf { hyp := 841, conc := 816, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 842, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 843, conc := 817, proof := sorry })
                    (RArray.leaf { hyp := 843, conc := 842, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 844, conc := 816, proof := sorry })
                  (RArray.leaf { hyp := 845, conc := 816, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 846, conc := 817, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 846, conc := 844, proof := sorry })
                    (RArray.leaf { hyp := 846, conc := 845, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 847, conc := 818, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 847, conc := 841, proof := sorry })
                    (RArray.leaf { hyp := 847, conc := 844, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 849, conc := 819, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 849, conc := 841, proof := sorry })
                    (RArray.leaf { hyp := 849, conc := 845, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 850, conc := 843, proof := sorry })
                  (RArray.leaf { hyp := 850, conc := 846, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 850, conc := 847, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 850, conc := 848, proof := sorry })
                    (RArray.leaf { hyp := 851, conc := 821, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 851, conc := 831, proof := sorry })
                  (RArray.leaf { hyp := 851, conc := 841, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 853, conc := 822, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 853, conc := 831, proof := sorry })
                    (RArray.leaf { hyp := 853, conc := 842, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 854, conc := 852, proof := sorry })
                  (RArray.leaf { hyp := 855, conc := 821, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 855, conc := 834, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 855, conc := 844, proof := sorry })
                    (RArray.leaf { hyp := 857, conc := 822, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 857, conc := 834, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 858, conc := 856, proof := sorry })
                    (RArray.leaf { hyp := 84, conc := 73, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 859, conc := 824, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 859, conc := 831, proof := sorry })
                    (RArray.leaf { hyp := 859, conc := 844, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 860, conc := 824, proof := sorry })
                  (RArray.leaf { hyp := 860, conc := 832, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 860, conc := 845, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 862, conc := 861, proof := sorry })
                    (RArray.leaf { hyp := 863, conc := 837, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 863, conc := 855, proof := sorry })
                  (RArray.leaf { hyp := 864, conc := 852, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 864, conc := 860, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 865, conc := 861, proof := sorry })
                    (RArray.leaf { hyp := 866, conc := 856, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 866, conc := 861, proof := sorry })
                  (RArray.leaf { hyp := 867, conc := 854, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 867, conc := 858, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 867, conc := 862, proof := sorry })
                    (RArray.leaf { hyp := 867, conc := 864, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 867, conc := 865, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 85, conc := 74, proof := sorry })
                    (RArray.leaf { hyp := 869, conc := 816, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 871, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 872, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 873, conc := 817, proof := sorry }))))))))))
  (RArray.branch 167
    (RArray.branch 83
      (RArray.branch 41
        (RArray.branch 20
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 874, conc := 868, proof := sorry })
                  (RArray.leaf { hyp := 877, conc := 870, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 877, conc := 875, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 877, conc := 876, proof := sorry })
                    (RArray.leaf { hyp := 878, conc := 816, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 86, conc := 65, proof := sorry })
                  (RArray.leaf { hyp := 881, conc := 816, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 882, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 886, conc := 878, proof := sorry })
                    (RArray.leaf { hyp := 886, conc := 882, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 887, conc := 880, proof := sorry })
                  (RArray.leaf { hyp := 887, conc := 885, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 888, conc := 868, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 87, conc := 75, proof := sorry })
                    (RArray.leaf { hyp := 890, conc := 879, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 891, conc := 890, proof := sorry })
                  (RArray.leaf { hyp := 895, conc := 893, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 896, conc := 868, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 897, conc := 824, proof := sorry })
                    (RArray.leaf { hyp := 897, conc := 869, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 897, conc := 882, proof := sorry })
                  (RArray.leaf { hyp := 899, conc := 883, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 900, conc := 884, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 901, conc := 893, proof := sorry })
                    (RArray.leaf { hyp := 902, conc := 890, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 902, conc := 894, proof := sorry })
                  (RArray.leaf { hyp := 903, conc := 898, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 904, conc := 903, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 905, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 906, conc := 816, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 909, conc := 816, proof := sorry })
                  (RArray.leaf { hyp := 913, conc := 905, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 913, conc := 909, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 914, conc := 907, proof := sorry })
                    (RArray.leaf { hyp := 914, conc := 910, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 915, conc := 816, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 916, conc := 816, proof := sorry })
                    (RArray.leaf { hyp := 918, conc := 816, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 90, conc := 62, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 920, conc := 919, proof := sorry })
                    (RArray.leaf { hyp := 924, conc := 917, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 924, conc := 922, proof := sorry })
                  (RArray.leaf { hyp := 924, conc := 923, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 928, conc := 917, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 91, conc := 75, proof := sorry })
                    (RArray.leaf { hyp := 932, conc := 931, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 933, conc := 824, proof := sorry })
                  (RArray.leaf { hyp := 933, conc := 905, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 933, conc := 918, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 934, conc := 906, proof := sorry })
                    (RArray.leaf { hyp := 936, conc := 934, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 936, conc := 935, proof := sorry })
                  (RArray.leaf { hyp := 937, conc := 911, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 937, conc := 925, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 92, conc := 63, proof := sorry })
                    (RArray.leaf { hyp := 941, conc := 924, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 941, conc := 928, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 941, conc := 932, proof := sorry })
                    (RArray.leaf { hyp := 941, conc := 936, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 941, conc := 938, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 941, conc := 939, proof := sorry })
                    (RArray.leaf { hyp := 941, conc := 940, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 945, conc := 943, proof := sorry })
                  (RArray.leaf { hyp := 948, conc := 832, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 948, conc := 871, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 948, conc := 909, proof := sorry })
                    (RArray.leaf { hyp := 93, conc := 67, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 949, conc := 947, proof := sorry })
                  (RArray.leaf { hyp := 953, conc := 870, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 954, conc := 942, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 954, conc := 950, proof := sorry })
                    (RArray.leaf { hyp := 955, conc := 947, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 956, conc := 838, proof := sorry })
                  (RArray.leaf { hyp := 956, conc := 874, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 956, conc := 952, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 957, conc := 947, proof := sorry })
                    (RArray.leaf { hyp := 958, conc := 877, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 958, conc := 949, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 958, conc := 955, proof := sorry })
                    (RArray.leaf { hyp := 958, conc := 956, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 958, conc := 957, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 94, conc := 90, proof := sorry })
                    (RArray.leaf { hyp := 959, conc := 831, proof := sorry }))))))))
      (RArray.branch 42
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 959, conc := 878, proof := sorry })
                  (RArray.leaf { hyp := 959, conc := 915, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 961, conc := 878, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 961, conc := 916, proof := sorry })
                    (RArray.leaf { hyp := 962, conc := 917, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 963, conc := 831, proof := sorry })
                  (RArray.leaf { hyp := 966, conc := 920, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 966, conc := 964, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 966, conc := 965, proof := sorry })
                    (RArray.leaf { hyp := 967, conc := 834, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 967, conc := 878, proof := sorry })
                  (RArray.leaf { hyp := 95, conc := 78, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 95, conc := 87, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 971, conc := 884, proof := sorry })
                    (RArray.leaf { hyp := 971, conc := 959, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 974, conc := 969, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 975, conc := 972, proof := sorry })
                    (RArray.leaf { hyp := 975, conc := 973, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 975, conc := 974, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 977, conc := 869, proof := sorry })
                    (RArray.leaf { hyp := 977, conc := 916, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 978, conc := 842, proof := sorry })
                  (RArray.leaf { hyp := 96, conc := 59, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 96, conc := 86, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 979, conc := 917, proof := sorry })
                    (RArray.leaf { hyp := 980, conc := 841, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 980, conc := 871, proof := sorry })
                  (RArray.leaf { hyp := 983, conc := 981, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 983, conc := 982, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 988, conc := 874, proof := sorry })
                    (RArray.leaf { hyp := 988, conc := 921, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 988, conc := 976, proof := sorry })
                  (RArray.leaf { hyp := 991, conc := 981, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 992, conc := 991, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 993, conc := 888, proof := sorry })
                    (RArray.leaf { hyp := 993, conc := 942, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 994, conc := 889, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 994, conc := 943, proof := sorry })
                    (RArray.leaf { hyp := 995, conc := 926, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 995, conc := 944, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 995, conc := 978, proof := sorry })
                    (RArray.leaf { hyp := 996, conc := 890, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 997, conc := 945, proof := sorry })
                  (RArray.leaf { hyp := 997, conc := 962, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 997, conc := 979, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 997, conc := 996, proof := sorry })
                    (RArray.leaf { hyp := 998, conc := 892, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 998, conc := 946, proof := sorry })
                  (RArray.leaf { hyp := 8, conc := 7, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1004, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1122, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1123, conc := 1, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1125, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1126, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1133, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1134, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1137, conc := 1, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 1138, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1141, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1142, conc := 1, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 1143, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1167, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1168, conc := 1, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1329, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1336, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1337, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1340, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1341, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1344, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1345, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1346, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1371, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1374, conc := 1, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1375, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1378, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1379, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1380, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1389, conc := 1, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 1391, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1392, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1395, conc := 1, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 1396, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1397, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1405, conc := 1, proof := sorry })))))))))
    (RArray.branch 83
      (RArray.branch 41
        (RArray.branch 20
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1406, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1407, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1410, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1411, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1412, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1415, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1416, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1417, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1420, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1421, conc := 1, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1422, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1423, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 143, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 146, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 147, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 148, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1529, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1531, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1532, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1539, conc := 1, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1540, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1543, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1544, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1731, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1732, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1735, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1743, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1747, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1751, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1752, conc := 1, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1777, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 1935, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1937, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1938, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 1945, conc := 1, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 1946, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 232, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 2340, conc := 1, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 2343, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 2344, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 3153, conc := 1, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 3155, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 3156, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 514, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 516, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 517, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 525, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 528, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 529, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 611, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 717, conc := 1, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 719, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 727, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 728, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 88, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 922, conc := 1, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 923, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 931, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 934, conc := 1, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 935, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 938, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 939, conc := 1, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 940, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 965, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 970, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 972, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 973, conc := 1, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 982, conc := 1, proof := sorry })
                  (RArray.leaf { hyp := 986, conc := 1, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 987, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 989, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 13, conc := 22, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 13, conc := 28, proof := sorry })
                  (RArray.leaf { hyp := 13, conc := 7, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 15, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 22, proof := sorry })
                    (RArray.leaf { hyp := 1570, conc := 2661, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 39, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 42, proof := sorry })
                    (RArray.leaf { hyp := 1570, conc := 4511, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 1570, conc := 7, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1688, conc := 1, proof := sorry })
                    (RArray.leaf { hyp := 28, conc := 13, proof := sorry }))))))))
      (RArray.branch 42
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 13, proof := sorry })
                  (RArray.leaf { hyp := 1, conc := 167, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 22, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 2, proof := sorry })
                    (RArray.leaf { hyp := 1, conc := 3721, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 3743, proof := sorry })
                  (RArray.leaf { hyp := 1, conc := 37, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 380, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 386, proof := sorry })
                    (RArray.leaf { hyp := 1, conc := 38, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 3, proof := sorry })
                  (RArray.leaf { hyp := 1, conc := 39, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 40, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 41, proof := sorry })
                    (RArray.leaf { hyp := 1, conc := 42, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 4511, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 4512, proof := sorry })
                    (RArray.leaf { hyp := 1, conc := 4521, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 4581, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 45, proof := sorry })
                    (RArray.leaf { hyp := 1, conc := 4, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 5, proof := sorry })
                  (RArray.leaf { hyp := 1, conc := 6, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 1, conc := 7, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 3721, proof := sorry })
                    (RArray.leaf { hyp := 3743, conc := 380, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 4511, proof := sorry })
                  (RArray.leaf { hyp := 386, conc := 42, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 37, conc := 41, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 38, conc := 380, proof := sorry })
                    (RArray.leaf { hyp := 38, conc := 44, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 22, proof := sorry })
                  (RArray.leaf { hyp := 2, conc := 3721, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 7, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3721, proof := sorry })
                    (RArray.leaf { hyp := 40, conc := 3743, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 380, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 38, proof := sorry })
                    (RArray.leaf { hyp := 40, conc := 39, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 45, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 41, conc := 37, proof := sorry })
                    (RArray.leaf { hyp := 4512, conc := 4511, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 4521, conc := 4512, proof := sorry })
                  (RArray.leaf { hyp := 4563, conc := 4511, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 4578, conc := 4511, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 4578, conc := 4563, proof := sorry })
                    (RArray.leaf { hyp := 4581, conc := 4521, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 4581, conc := 4563, proof := sorry })
                  (RArray.leaf { hyp := 4581, conc := 4578, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 44, conc := 380, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 44, conc := 38, proof := sorry })
                    (RArray.leaf { hyp := 45, conc := 3721, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 3743, proof := sorry })
                  (RArray.leaf { hyp := 45, conc := 380, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 386, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 38, proof := sorry })
                    (RArray.leaf { hyp := 45, conc := 39, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 40, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 41, proof := sorry })
                    (RArray.leaf { hyp := 45, conc := 4581, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 22, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 2, proof := sorry })
                    (RArray.leaf { hyp := 3, conc := 3721, proof := sorry }))))))
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 3743, proof := sorry })
                  (RArray.leaf { hyp := 3, conc := 380, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 41, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 4521, proof := sorry })
                    (RArray.leaf { hyp := 3, conc := 7, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 22, proof := sorry })
                  (RArray.leaf { hyp := 4, conc := 2, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 3721, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 3743, proof := sorry })
                    (RArray.leaf { hyp := 4, conc := 380, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 38, proof := sorry })
                  (RArray.leaf { hyp := 4, conc := 4511, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 4563, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 4, conc := 4578, proof := sorry })
                    (RArray.leaf { hyp := 4, conc := 7, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { hyp := 5, conc := 1, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 5, conc := 2, proof := sorry })
                    (RArray.leaf { hyp := 6, conc := 1, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { hyp := 6, conc := 2, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { hyp := 6, conc := 40, proof := sorry })
                    (RArray.leaf { hyp := 952, conc := 1, proof := sorry }))))))))))

end EndToEnd
