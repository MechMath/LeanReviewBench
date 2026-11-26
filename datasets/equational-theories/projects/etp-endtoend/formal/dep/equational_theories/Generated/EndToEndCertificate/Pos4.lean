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
def _root_.EndToEnd.pos4 : RArray EndToEnd.PosFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3672, conc := 3671, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3673, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3674, conc := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3676, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3677, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 366, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3679, conc := 3660, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3679, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3679, conc := 3676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3682, conc := 3675, proof := sorry })
                      (RArray.leaf { hyp := 3682, conc := 3678, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3682, conc := 3680, proof := sorry })
                      (RArray.leaf { hyp := 3683, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3684, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3686, conc := 3658, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3687, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3689, conc := 3660, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3689, conc := 3683, proof := sorry })
                      (RArray.leaf { hyp := 3689, conc := 3686, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3690, conc := 3684, proof := sorry })
                      (RArray.leaf { hyp := 3691, conc := 3687, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3692, conc := 3662, proof := sorry })
                      (RArray.leaf { hyp := 3692, conc := 3685, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3692, conc := 3688, proof := sorry })
                      (RArray.leaf { hyp := 3692, conc := 3689, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3692, conc := 3690, proof := sorry })
                      (RArray.leaf { hyp := 3693, conc := 3663, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3693, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3693, conc := 3683, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3697, conc := 3663, proof := sorry })
                      (RArray.leaf { hyp := 3697, conc := 3676, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3697, conc := 3686, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3698, conc := 3677, proof := sorry })
                      (RArray.leaf { hyp := 368, conc := 366, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 368, conc := 367, proof := sorry })
                      (RArray.leaf { hyp := 3699, conc := 3664, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3699, conc := 3676, proof := sorry })
                      (RArray.leaf { hyp := 3699, conc := 3687, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3700, conc := 3665, proof := sorry })
                      (RArray.leaf { hyp := 3700, conc := 3678, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3700, conc := 3688, proof := sorry })
                      (RArray.leaf { hyp := 3700, conc := 3697, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3700, conc := 3698, proof := sorry })
                      (RArray.leaf { hyp := 3701, conc := 3666, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3701, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3701, conc := 3686, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3702, conc := 3666, proof := sorry })
                      (RArray.leaf { hyp := 3702, conc := 3674, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3704, conc := 3668, proof := sorry })
                      (RArray.leaf { hyp := 3704, conc := 3675, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3704, conc := 3688, proof := sorry })
                      (RArray.leaf { hyp := 3704, conc := 3701, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3704, conc := 3702, proof := sorry })
                      (RArray.leaf { hyp := 3704, conc := 3703, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3705, conc := 3669, proof := sorry })
                      (RArray.leaf { hyp := 3705, conc := 3679, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3705, conc := 3689, proof := sorry })
                      (RArray.leaf { hyp := 3705, conc := 3693, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3705, conc := 3697, proof := sorry })
                      (RArray.leaf { hyp := 3705, conc := 3701, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3706, conc := 3669, proof := sorry })
                      (RArray.leaf { hyp := 3706, conc := 3680, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3706, conc := 3690, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3706, conc := 3694, proof := sorry })
                      (RArray.leaf { hyp := 3706, conc := 3698, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3706, conc := 3702, proof := sorry })
                      (RArray.leaf { hyp := 3707, conc := 3670, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3707, conc := 3679, proof := sorry })
                      (RArray.leaf { hyp := 3707, conc := 3690, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3707, conc := 3695, proof := sorry })
                      (RArray.leaf { hyp := 3707, conc := 3703, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3708, conc := 3671, proof := sorry })
                      (RArray.leaf { hyp := 3708, conc := 3681, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3708, conc := 3691, proof := sorry })
                      (RArray.leaf { hyp := 3708, conc := 3693, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3708, conc := 3698, proof := sorry })
                      (RArray.leaf { hyp := 3708, conc := 3703, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 369, conc := 360, proof := sorry })
                      (RArray.leaf { hyp := 369, conc := 363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3709, conc := 3672, proof := sorry })
                      (RArray.leaf { hyp := 3709, conc := 3682, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3709, conc := 3705, proof := sorry })
                      (RArray.leaf { hyp := 3709, conc := 3707, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3711, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3712, conc := 3710, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3713, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3714, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3715, conc := 3659, proof := sorry })
                      (RArray.leaf { hyp := 3715, conc := 3713, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3715, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 3716, conc := 3710, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3717, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 3717, conc := 3711, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3717, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 3718, conc := 3710, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 370, conc := 360, proof := sorry })
                      (RArray.leaf { hyp := 370, conc := 364, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3719, conc := 3712, proof := sorry })
                      (RArray.leaf { hyp := 3719, conc := 3718, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3720, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3721, conc := 3658, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3722, conc := 3659, proof := sorry })
                      (RArray.leaf { hyp := 3722, conc := 3720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3722, conc := 3721, proof := sorry })
                      (RArray.leaf { hyp := 3723, conc := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3724, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3725, conc := 3659, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3725, conc := 3723, proof := sorry })
                      (RArray.leaf { hyp := 3725, conc := 3724, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3726, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 3726, conc := 3720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3727, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 3727, conc := 3721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3727, conc := 3724, proof := sorry })
                      (RArray.leaf { hyp := 3728, conc := 3661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3728, conc := 3720, proof := sorry })
                      (RArray.leaf { hyp := 3728, conc := 3724, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 371, conc := 361, proof := sorry })
                      (RArray.leaf { hyp := 371, conc := 363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 371, conc := 367, proof := sorry })
                      (RArray.leaf { hyp := 3729, conc := 3662, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3729, conc := 3722, proof := sorry })
                      (RArray.leaf { hyp := 3729, conc := 3726, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3729, conc := 3727, proof := sorry })
                      (RArray.leaf { hyp := 3729, conc := 3728, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3731, conc := 3663, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3731, conc := 3711, proof := sorry })
                      (RArray.leaf { hyp := 3731, conc := 3721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3732, conc := 3710, proof := sorry })
                      (RArray.leaf { hyp := 3733, conc := 3730, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3733, conc := 3732, proof := sorry })
                      (RArray.leaf { hyp := 3735, conc := 3663, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3735, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 3735, conc := 3724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3736, conc := 3664, proof := sorry })
                      (RArray.leaf { hyp := 3736, conc := 3713, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3736, conc := 3724, proof := sorry })
                      (RArray.leaf { hyp := 3737, conc := 3665, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3737, conc := 3715, proof := sorry })
                      (RArray.leaf { hyp := 3737, conc := 3725, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3737, conc := 3734, proof := sorry })
                      (RArray.leaf { hyp := 3737, conc := 3735, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3737, conc := 3736, proof := sorry })
                      (RArray.leaf { hyp := 3738, conc := 3710, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 372, conc := 362, proof := sorry })
                      (RArray.leaf { hyp := 372, conc := 365, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 372, conc := 370, proof := sorry })
                      (RArray.leaf { hyp := 3739, conc := 3666, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3739, conc := 3711, proof := sorry })
                      (RArray.leaf { hyp := 3739, conc := 3724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3740, conc := 3710, proof := sorry })
                      (RArray.leaf { hyp := 3741, conc := 3738, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3741, conc := 3740, proof := sorry })
                      (RArray.leaf { hyp := 3742, conc := 3716, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3742, conc := 3730, proof := sorry })
                      (RArray.leaf { hyp := 3743, conc := 3669, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 3717, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 3727, proof := sorry })
                      (RArray.leaf { hyp := 3743, conc := 3731, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 3735, proof := sorry })
                      (RArray.leaf { hyp := 3743, conc := 3739, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3744, conc := 3740, proof := sorry })
                      (RArray.leaf { hyp := 3745, conc := 3718, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3745, conc := 3730, proof := sorry })
                      (RArray.leaf { hyp := 3746, conc := 3737, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3746, conc := 3743, proof := sorry })
                      (RArray.leaf { hyp := 3746, conc := 3745, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3747, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3748, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3751, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3755, conc := 3747, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3755, conc := 3751, proof := sorry })
                      (RArray.leaf { hyp := 3756, conc := 3749, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3756, conc := 3752, proof := sorry })
                      (RArray.leaf { hyp := 3756, conc := 3753, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3758, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 374, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3760, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 3764, conc := 3761, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3766, conc := 3759, proof := sorry })
                      (RArray.leaf { hyp := 3766, conc := 3762, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3766, conc := 3763, proof := sorry })
                      (RArray.leaf { hyp := 3766, conc := 3765, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3768, conc := 3663, proof := sorry })
                      (RArray.leaf { hyp := 3768, conc := 3758, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 375, conc := 373, proof := sorry })
                      (RArray.leaf { hyp := 3770, conc := 3759, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3772, conc := 3761, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3774, conc := 3773, proof := sorry })
                      (RArray.leaf { hyp := 3775, conc := 3666, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3775, conc := 3747, proof := sorry })
                      (RArray.leaf { hyp := 3775, conc := 3760, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3776, conc := 3761, proof := sorry })
                      (RArray.leaf { hyp := 3778, conc := 3762, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 376, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3779, conc := 3753, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3780, conc := 3764, proof := sorry })
                      (RArray.leaf { hyp := 3780, conc := 3776, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3781, conc := 3773, proof := sorry })
                      (RArray.leaf { hyp := 3782, conc := 3767, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3782, conc := 3777, proof := sorry })
                      (RArray.leaf { hyp := 3783, conc := 3756, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3783, conc := 3766, proof := sorry })
                      (RArray.leaf { hyp := 3783, conc := 3770, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3783, conc := 3774, proof := sorry })
                      (RArray.leaf { hyp := 3783, conc := 3778, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3783, conc := 3779, proof := sorry })
                      (RArray.leaf { hyp := 3783, conc := 3781, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3785, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3785, conc := 3711, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3785, conc := 3748, proof := sorry })
                      (RArray.leaf { hyp := 3787, conc := 3786, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 377, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 3789, conc := 3673, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3789, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 3789, conc := 3751, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3791, conc := 3752, proof := sorry })
                      (RArray.leaf { hyp := 3792, conc := 3750, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3793, conc := 3676, proof := sorry })
                      (RArray.leaf { hyp := 3793, conc := 3711, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3793, conc := 3751, proof := sorry })
                      (RArray.leaf { hyp := 3795, conc := 3678, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3795, conc := 3792, proof := sorry })
                      (RArray.leaf { hyp := 3796, conc := 3792, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3797, conc := 3679, proof := sorry })
                      (RArray.leaf { hyp := 3797, conc := 3717, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3797, conc := 3754, proof := sorry })
                      (RArray.leaf { hyp := 3797, conc := 3785, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3797, conc := 3789, proof := sorry })
                      (RArray.leaf { hyp := 3797, conc := 3793, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3798, conc := 3794, proof := sorry })
                      (RArray.leaf { hyp := 378, conc := 359, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 378, conc := 376, proof := sorry })
                      (RArray.leaf { hyp := 378, conc := 377, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 36, conc := 32, proof := sorry })
                      (RArray.leaf { hyp := 36, conc := 34, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 36, conc := 35, proof := sorry })
                      (RArray.leaf { hyp := 3799, conc := 3794, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3800, conc := 3795, proof := sorry })
                      (RArray.leaf { hyp := 3800, conc := 3798, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3802, conc := 3673, proof := sorry })
                      (RArray.leaf { hyp := 3802, conc := 3721, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3802, conc := 3758, proof := sorry })
                      (RArray.leaf { hyp := 3804, conc := 3801, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3806, conc := 3761, proof := sorry })
                      (RArray.leaf { hyp := 3808, conc := 3762, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3808, conc := 3807, proof := sorry })
                      (RArray.leaf { hyp := 3812, conc := 3762, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3813, conc := 3763, proof := sorry })
                      (RArray.leaf { hyp := 3814, conc := 3810, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3815, conc := 3807, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3816, conc := 3811, proof := sorry })
                      (RArray.leaf { hyp := 3817, conc := 3812, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3817, conc := 3815, proof := sorry })
                      (RArray.leaf { hyp := 380, conc := 360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 380, conc := 374, proof := sorry })
                      (RArray.leaf { hyp := 380, conc := 377, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3819, conc := 3683, proof := sorry })
                      (RArray.leaf { hyp := 3819, conc := 3711, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3819, conc := 3758, proof := sorry })
                      (RArray.leaf { hyp := 3821, conc := 3820, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3822, conc := 3713, proof := sorry })
                      (RArray.leaf { hyp := 3822, conc := 3760, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3823, conc := 3761, proof := sorry })
                      (RArray.leaf { hyp := 3825, conc := 3824, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3827, conc := 3761, proof := sorry })
                      (RArray.leaf { hyp := 3828, conc := 3687, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 381, conc := 373, proof := sorry })
                      (RArray.leaf { hyp := 3829, conc := 3762, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3829, conc := 3826, proof := sorry })
                      (RArray.leaf { hyp := 3829, conc := 3828, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3830, conc := 3763, proof := sorry })
                      (RArray.leaf { hyp := 3831, conc := 3827, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3832, conc := 3824, proof := sorry })
                      (RArray.leaf { hyp := 3833, conc := 3765, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3834, conc := 3821, proof := sorry })
                      (RArray.leaf { hyp := 3834, conc := 3825, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3834, conc := 3829, proof := sorry })
                      (RArray.leaf { hyp := 3834, conc := 3830, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3834, conc := 3832, proof := sorry })
                      (RArray.leaf { hyp := 3834, conc := 3833, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3835, conc := 3784, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3835, conc := 3801, proof := sorry })
                      (RArray.leaf { hyp := 3835, conc := 3818, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3836, conc := 3693, proof := sorry })
                      (RArray.leaf { hyp := 3836, conc := 3731, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3836, conc := 3768, proof := sorry })
                      (RArray.leaf { hyp := 3836, conc := 3802, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3836, conc := 3819, proof := sorry })
                      (RArray.leaf { hyp := 3837, conc := 3786, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3838, conc := 3820, proof := sorry })
                      (RArray.leaf { hyp := 382, conc := 375, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 382, conc := 379, proof := sorry })
                      (RArray.leaf { hyp := 3839, conc := 3787, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3839, conc := 3804, proof := sorry })
                      (RArray.leaf { hyp := 3839, conc := 3837, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3839, conc := 3838, proof := sorry })
                      (RArray.leaf { hyp := 3840, conc := 3771, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3840, conc := 3788, proof := sorry })
                      (RArray.leaf { hyp := 3840, conc := 3805, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3841, conc := 3772, proof := sorry })
                      (RArray.leaf { hyp := 3841, conc := 3806, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3841, conc := 3823, proof := sorry })
                      (RArray.leaf { hyp := 3842, conc := 3807, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3843, conc := 3773, proof := sorry })
                      (RArray.leaf { hyp := 3844, conc := 3791, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3844, conc := 3808, proof := sorry })
                      (RArray.leaf { hyp := 3844, conc := 3842, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3844, conc := 3843, proof := sorry })
                      (RArray.leaf { hyp := 3845, conc := 3792, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3846, conc := 3810, proof := sorry })
                      (RArray.leaf { hyp := 3847, conc := 3794, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 383, conc := 358, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3849, conc := 3812, proof := sorry })
                      (RArray.leaf { hyp := 3849, conc := 3848, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3850, conc := 3805, proof := sorry })
                      (RArray.leaf { hyp := 3851, conc := 3776, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3852, conc := 3807, proof := sorry })
                      (RArray.leaf { hyp := 3853, conc := 3777, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3854, conc := 3778, proof := sorry })
                      (RArray.leaf { hyp := 3854, conc := 3852, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3855, conc := 3796, proof := sorry })
                      (RArray.leaf { hyp := 3855, conc := 3813, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3855, conc := 3845, proof := sorry })
                      (RArray.leaf { hyp := 3855, conc := 3850, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3856, conc := 3780, proof := sorry })
                      (RArray.leaf { hyp := 3856, conc := 3814, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3856, conc := 3851, proof := sorry })
                      (RArray.leaf { hyp := 3857, conc := 3852, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3858, conc := 3848, proof := sorry })
                      (RArray.leaf { hyp := 384, conc := 358, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3859, conc := 3782, proof := sorry })
                      (RArray.leaf { hyp := 3859, conc := 3799, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3859, conc := 3816, proof := sorry })
                      (RArray.leaf { hyp := 3859, conc := 3847, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3859, conc := 3853, proof := sorry })
                      (RArray.leaf { hyp := 3860, conc := 3783, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3860, conc := 3800, proof := sorry })
                      (RArray.leaf { hyp := 3860, conc := 3849, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3860, conc := 3854, proof := sorry })
                      (RArray.leaf { hyp := 3860, conc := 3857, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3860, conc := 3858, proof := sorry })
                      (RArray.leaf { hyp := 3862, conc := 3861, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3863, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3864, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3865, conc := 3862, proof := sorry })
                      (RArray.leaf { hyp := 3865, conc := 3863, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3865, conc := 3864, proof := sorry })
                      (RArray.leaf { hyp := 3866, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3867, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3868, conc := 3866, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3868, conc := 3867, proof := sorry })
                      (RArray.leaf { hyp := 3869, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3870, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3871, conc := 3862, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3871, conc := 3869, proof := sorry })
                      (RArray.leaf { hyp := 3871, conc := 3870, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3872, conc := 3863, proof := sorry })
                      (RArray.leaf { hyp := 3872, conc := 3866, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3872, conc := 3869, proof := sorry })
                      (RArray.leaf { hyp := 3873, conc := 3863, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3873, conc := 3867, proof := sorry })
                      (RArray.leaf { hyp := 3873, conc := 3870, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3874, conc := 3864, proof := sorry })
                      (RArray.leaf { hyp := 3874, conc := 3866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3875, conc := 3865, proof := sorry })
                      (RArray.leaf { hyp := 3875, conc := 3868, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3875, conc := 3872, proof := sorry })
                      (RArray.leaf { hyp := 3875, conc := 3873, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3875, conc := 3874, proof := sorry })
                      (RArray.leaf { hyp := 3876, conc := 3861, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3877, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 386, conc := 358, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3879, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3880, conc := 3861, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3882, conc := 3863, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3882, conc := 3876, proof := sorry })
                      (RArray.leaf { hyp := 3882, conc := 3879, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3885, conc := 3881, proof := sorry })
                      (RArray.leaf { hyp := 3885, conc := 3883, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3885, conc := 3884, proof := sorry })
                      (RArray.leaf { hyp := 3886, conc := 3861, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3887, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3889, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3891, conc := 3862, proof := sorry })
                      (RArray.leaf { hyp := 3892, conc := 3863, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3892, conc := 3886, proof := sorry })
                      (RArray.leaf { hyp := 3892, conc := 3889, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3893, conc := 3863, proof := sorry })
                      (RArray.leaf { hyp := 3893, conc := 3887, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3893, conc := 3890, proof := sorry })
                      (RArray.leaf { hyp := 3894, conc := 3864, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3894, conc := 3886, proof := sorry })
                      (RArray.leaf { hyp := 3894, conc := 3890, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3895, conc := 3865, proof := sorry })
                      (RArray.leaf { hyp := 3895, conc := 3888, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3895, conc := 3892, proof := sorry })
                      (RArray.leaf { hyp := 3895, conc := 3893, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3895, conc := 3894, proof := sorry })
                      (RArray.leaf { hyp := 3896, conc := 3866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3896, conc := 3876, proof := sorry })
                      (RArray.leaf { hyp := 3896, conc := 3886, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3900, conc := 3866, proof := sorry })
                      (RArray.leaf { hyp := 3900, conc := 3879, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3900, conc := 3889, proof := sorry })
                      (RArray.leaf { hyp := 3901, conc := 3866, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3901, conc := 3880, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3901, conc := 3890, proof := sorry })
                      (RArray.leaf { hyp := 3902, conc := 3867, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3902, conc := 3879, proof := sorry })
                      (RArray.leaf { hyp := 3902, conc := 3890, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3903, conc := 3868, proof := sorry })
                      (RArray.leaf { hyp := 3903, conc := 3881, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3903, conc := 3891, proof := sorry })
                      (RArray.leaf { hyp := 3903, conc := 3900, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3903, conc := 3901, proof := sorry })
                      (RArray.leaf { hyp := 3903, conc := 3902, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3904, conc := 3869, proof := sorry })
                      (RArray.leaf { hyp := 3904, conc := 3876, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3904, conc := 3889, proof := sorry })
                      (RArray.leaf { hyp := 3905, conc := 3869, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3905, conc := 3877, proof := sorry })
                      (RArray.leaf { hyp := 3905, conc := 3890, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3906, conc := 3870, proof := sorry })
                      (RArray.leaf { hyp := 3906, conc := 3890, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3907, conc := 3878, proof := sorry })
                      (RArray.leaf { hyp := 3907, conc := 3891, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3908, conc := 3872, proof := sorry })
                      (RArray.leaf { hyp := 3908, conc := 3882, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3908, conc := 3892, proof := sorry })
                      (RArray.leaf { hyp := 3908, conc := 3896, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3908, conc := 3900, proof := sorry })
                      (RArray.leaf { hyp := 3908, conc := 3904, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 389, conc := 386, proof := sorry })
                      (RArray.leaf { hyp := 3909, conc := 3883, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3910, conc := 3873, proof := sorry })
                      (RArray.leaf { hyp := 3910, conc := 3882, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3910, conc := 3893, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3910, conc := 3898, proof := sorry })
                      (RArray.leaf { hyp := 3910, conc := 3902, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3910, conc := 3906, proof := sorry })
                      (RArray.leaf { hyp := 3911, conc := 3874, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3911, conc := 3884, proof := sorry })
                      (RArray.leaf { hyp := 3911, conc := 3894, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3911, conc := 3896, proof := sorry })
                      (RArray.leaf { hyp := 3911, conc := 3901, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3911, conc := 3906, proof := sorry })
                      (RArray.leaf { hyp := 3912, conc := 3875, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3912, conc := 3885, proof := sorry })
                      (RArray.leaf { hyp := 3912, conc := 3895, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3912, conc := 3908, proof := sorry })
                      (RArray.leaf { hyp := 3912, conc := 3910, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3914, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3915, conc := 3913, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3916, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3917, conc := 3861, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3918, conc := 3862, proof := sorry })
                      (RArray.leaf { hyp := 3918, conc := 3916, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3918, conc := 3917, proof := sorry })
                      (RArray.leaf { hyp := 390, conc := 387, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3919, conc := 3913, proof := sorry })
                      (RArray.leaf { hyp := 3920, conc := 3863, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3920, conc := 3914, proof := sorry })
                      (RArray.leaf { hyp := 3920, conc := 3917, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3921, conc := 3913, proof := sorry })
                      (RArray.leaf { hyp := 3922, conc := 3915, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3922, conc := 3919, proof := sorry })
                      (RArray.leaf { hyp := 3922, conc := 3921, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3923, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3924, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3925, conc := 3862, proof := sorry })
                      (RArray.leaf { hyp := 3925, conc := 3923, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3925, conc := 3924, proof := sorry })
                      (RArray.leaf { hyp := 3926, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3927, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3928, conc := 3862, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3928, conc := 3926, proof := sorry })
                      (RArray.leaf { hyp := 3928, conc := 3927, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3929, conc := 3863, proof := sorry })
                      (RArray.leaf { hyp := 3929, conc := 3923, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3929, conc := 3926, proof := sorry })
                      (RArray.leaf { hyp := 3930, conc := 3863, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3930, conc := 3924, proof := sorry })
                      (RArray.leaf { hyp := 3930, conc := 3927, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3931, conc := 3864, proof := sorry })
                      (RArray.leaf { hyp := 3931, conc := 3923, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3931, conc := 3927, proof := sorry })
                      (RArray.leaf { hyp := 3932, conc := 3865, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3932, conc := 3925, proof := sorry })
                      (RArray.leaf { hyp := 3932, conc := 3928, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3932, conc := 3929, proof := sorry })
                      (RArray.leaf { hyp := 3932, conc := 3930, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3932, conc := 3931, proof := sorry })
                      (RArray.leaf { hyp := 3933, conc := 3913, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3934, conc := 3866, proof := sorry })
                      (RArray.leaf { hyp := 3934, conc := 3914, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3934, conc := 3924, proof := sorry })
                      (RArray.leaf { hyp := 3935, conc := 3913, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3936, conc := 3933, proof := sorry })
                      (RArray.leaf { hyp := 3936, conc := 3935, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3938, conc := 3866, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3938, conc := 3917, proof := sorry })
                      (RArray.leaf { hyp := 3938, conc := 3927, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 392, conc := 385, proof := sorry })
                      (RArray.leaf { hyp := 392, conc := 389, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 392, conc := 391, proof := sorry })
                      (RArray.leaf { hyp := 3939, conc := 3867, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 3916, proof := sorry })
                      (RArray.leaf { hyp := 3940, conc := 3918, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3940, conc := 3937, proof := sorry })
                      (RArray.leaf { hyp := 3941, conc := 3913, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3942, conc := 3869, proof := sorry })
                      (RArray.leaf { hyp := 3942, conc := 3914, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3942, conc := 3927, proof := sorry })
                      (RArray.leaf { hyp := 3943, conc := 3913, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3944, conc := 3941, proof := sorry })
                      (RArray.leaf { hyp := 3944, conc := 3943, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3945, conc := 3941, proof := sorry })
                      (RArray.leaf { hyp := 3946, conc := 3872, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3946, conc := 3920, proof := sorry })
                      (RArray.leaf { hyp := 3946, conc := 3930, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3946, conc := 3934, proof := sorry })
                      (RArray.leaf { hyp := 3946, conc := 3938, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3946, conc := 3942, proof := sorry })
                      (RArray.leaf { hyp := 3947, conc := 3939, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3947, conc := 3943, proof := sorry })
                      (RArray.leaf { hyp := 3948, conc := 3943, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 393, conc := 383, proof := sorry })
                      (RArray.leaf { hyp := 3949, conc := 3922, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3949, conc := 3936, proof := sorry })
                      (RArray.leaf { hyp := 3949, conc := 3940, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3949, conc := 3947, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3949, conc := 3948, proof := sorry })
                      (RArray.leaf { hyp := 3950, conc := 3861, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3951, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3953, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3954, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3958, conc := 3864, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3958, conc := 3950, proof := sorry })
                      (RArray.leaf { hyp := 394, conc := 374, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3959, conc := 3952, proof := sorry })
                      (RArray.leaf { hyp := 3959, conc := 3956, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3960, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3961, conc := 3861, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3963, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3967, conc := 3964, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3969, conc := 3962, proof := sorry })
                      (RArray.leaf { hyp := 3969, conc := 3965, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3969, conc := 3968, proof := sorry })
                      (RArray.leaf { hyp := 3971, conc := 3866, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3971, conc := 3951, proof := sorry })
                      (RArray.leaf { hyp := 3971, conc := 3961, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3972, conc := 3867, proof := sorry })
                      (RArray.leaf { hyp := 3972, conc := 3950, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3973, conc := 3970, proof := sorry })
                      (RArray.leaf { hyp := 3977, conc := 3976, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3978, conc := 3950, proof := sorry })
                      (RArray.leaf { hyp := 3978, conc := 3963, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 396, conc := 395, proof := sorry })
                      (RArray.leaf { hyp := 3982, conc := 3966, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3983, conc := 3957, proof := sorry })
                      (RArray.leaf { hyp := 3983, conc := 3979, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3986, conc := 3959, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3986, conc := 3969, proof := sorry })
                      (RArray.leaf { hyp := 3986, conc := 3973, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3986, conc := 3977, proof := sorry })
                      (RArray.leaf { hyp := 3986, conc := 3982, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3986, conc := 3984, proof := sorry })
                      (RArray.leaf { hyp := 3986, conc := 3985, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3988, conc := 3876, proof := sorry })
                      (RArray.leaf { hyp := 3988, conc := 3914, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3988, conc := 3951, proof := sorry })
                      (RArray.leaf { hyp := 3990, conc := 3989, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3992, conc := 3876, proof := sorry })
                      (RArray.leaf { hyp := 3992, conc := 3917, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3992, conc := 3954, proof := sorry })
                      (RArray.leaf { hyp := 3993, conc := 3877, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3993, conc := 3916, proof := sorry })
                      (RArray.leaf { hyp := 3993, conc := 3954, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3994, conc := 3991, proof := sorry })
                      (RArray.leaf { hyp := 3995, conc := 3953, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3996, conc := 3879, proof := sorry })
                      (RArray.leaf { hyp := 3996, conc := 3914, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3996, conc := 3954, proof := sorry })
                      (RArray.leaf { hyp := 3998, conc := 3997, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 398, conc := 387, proof := sorry })
                      (RArray.leaf { hyp := 3999, conc := 3956, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3999, conc := 3995, proof := sorry })
                      (RArray.leaf { hyp := 4000, conc := 3882, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4000, conc := 3920, proof := sorry })
                      (RArray.leaf { hyp := 4000, conc := 3957, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4000, conc := 3988, proof := sorry })
                      (RArray.leaf { hyp := 4000, conc := 3992, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4000, conc := 3996, proof := sorry })
                      (RArray.leaf { hyp := 4001, conc := 3989, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4001, conc := 3997, proof := sorry })
                      (RArray.leaf { hyp := 4002, conc := 3987, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4003, conc := 3994, proof := sorry })
                      (RArray.leaf { hyp := 4003, conc := 3999, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4004, conc := 3960, proof := sorry })
                      (RArray.leaf { hyp := 4005, conc := 3876, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4005, conc := 3924, proof := sorry })
                      (RArray.leaf { hyp := 4005, conc := 3961, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4006, conc := 3877, proof := sorry })
                      (RArray.leaf { hyp := 4006, conc := 3923, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4006, conc := 3961, proof := sorry })
                      (RArray.leaf { hyp := 4007, conc := 4004, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4011, conc := 4010, proof := sorry })
                      (RArray.leaf { hyp := 4012, conc := 3923, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4016, conc := 3929, proof := sorry })
                      (RArray.leaf { hyp := 4016, conc := 3966, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4017, conc := 4009, proof := sorry })
                      (RArray.leaf { hyp := 4017, conc := 4013, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4018, conc := 4014, proof := sorry })
                      (RArray.leaf { hyp := 400, conc := 365, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 400, conc := 399, proof := sorry })
                      (RArray.leaf { hyp := 4020, conc := 4016, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4022, conc := 3886, proof := sorry })
                      (RArray.leaf { hyp := 4022, conc := 3914, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4022, conc := 3961, proof := sorry })
                      (RArray.leaf { hyp := 4024, conc := 4023, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4025, conc := 3916, proof := sorry })
                      (RArray.leaf { hyp := 4025, conc := 3963, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4032, conc := 4029, proof := sorry })
                      (RArray.leaf { hyp := 4032, conc := 4031, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4033, conc := 3966, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4033, conc := 4021, proof := sorry })
                      (RArray.leaf { hyp := 4034, conc := 4026, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4034, conc := 4030, proof := sorry })
                      (RArray.leaf { hyp := 4035, conc := 4023, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4035, conc := 4027, proof := sorry })
                      (RArray.leaf { hyp := 4036, conc := 4021, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4037, conc := 4028, proof := sorry })
                      (RArray.leaf { hyp := 4037, conc := 4033, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4038, conc := 3970, proof := sorry })
                      (RArray.leaf { hyp := 402, conc := 387, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4039, conc := 3896, proof := sorry })
                      (RArray.leaf { hyp := 4039, conc := 3934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4039, conc := 3971, proof := sorry })
                      (RArray.leaf { hyp := 4039, conc := 3988, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4039, conc := 4005, proof := sorry })
                      (RArray.leaf { hyp := 4039, conc := 4022, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4040, conc := 3989, proof := sorry })
                      (RArray.leaf { hyp := 4040, conc := 4023, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4041, conc := 3987, proof := sorry })
                      (RArray.leaf { hyp := 4042, conc := 4038, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4043, conc := 3974, proof := sorry })
                      (RArray.leaf { hyp := 4047, conc := 4028, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4048, conc := 3974, proof := sorry })
                      (RArray.leaf { hyp := 4050, conc := 3997, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4051, conc := 3902, proof := sorry })
                      (RArray.leaf { hyp := 4051, conc := 3995, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4052, conc := 4015, proof := sorry })
                      (RArray.leaf { hyp := 4052, conc := 4048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4053, conc := 3987, proof := sorry })
                      (RArray.leaf { hyp := 4055, conc := 3989, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4056, conc := 3987, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4057, conc := 4011, proof := sorry })
                      (RArray.leaf { hyp := 4057, conc := 4053, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4058, conc := 3999, proof := sorry })
                      (RArray.leaf { hyp := 4058, conc := 4016, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4058, conc := 4033, proof := sorry })
                      (RArray.leaf { hyp := 4058, conc := 4038, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4058, conc := 4043, proof := sorry })
                      (RArray.leaf { hyp := 4058, conc := 4048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 404, conc := 401, proof := sorry })
                      (RArray.leaf { hyp := 404, conc := 403, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4059, conc := 3983, proof := sorry })
                      (RArray.leaf { hyp := 4059, conc := 4017, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4059, conc := 4034, proof := sorry })
                      (RArray.leaf { hyp := 4059, conc := 4044, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4059, conc := 4049, proof := sorry })
                      (RArray.leaf { hyp := 4059, conc := 4054, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4060, conc := 4001, proof := sorry })
                      (RArray.leaf { hyp := 4060, conc := 4018, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4060, conc := 4035, proof := sorry })
                      (RArray.leaf { hyp := 4060, conc := 4040, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4060, conc := 4045, proof := sorry })
                      (RArray.leaf { hyp := 4061, conc := 3999, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4061, conc := 4041, proof := sorry })
                      (RArray.leaf { hyp := 4061, conc := 4046, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4062, conc := 4002, proof := sorry })
                      (RArray.leaf { hyp := 4062, conc := 4019, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4062, conc := 4038, proof := sorry })
                      (RArray.leaf { hyp := 4063, conc := 3986, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4063, conc := 4003, proof := sorry })
                      (RArray.leaf { hyp := 4063, conc := 4020, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4063, conc := 4042, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4063, conc := 4047, proof := sorry })
                      (RArray.leaf { hyp := 4063, conc := 4058, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4065, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4066, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4067, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4068, conc := 4065, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4068, conc := 4066, proof := sorry })
                      (RArray.leaf { hyp := 4068, conc := 4067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 405, conc := 379, proof := sorry })
                      (RArray.leaf { hyp := 4069, conc := 4064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4070, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4071, conc := 4069, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4071, conc := 4070, proof := sorry })
                      (RArray.leaf { hyp := 4072, conc := 4064, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4073, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4074, conc := 4072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4074, conc := 4073, proof := sorry })
                      (RArray.leaf { hyp := 4075, conc := 4066, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4075, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4075, conc := 4072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4076, conc := 4070, proof := sorry })
                      (RArray.leaf { hyp := 4076, conc := 4073, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4077, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4077, conc := 4073, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4078, conc := 4071, proof := sorry })
                      (RArray.leaf { hyp := 4078, conc := 4074, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4078, conc := 4075, proof := sorry })
                      (RArray.leaf { hyp := 4078, conc := 4076, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4078, conc := 4077, proof := sorry })
                      (RArray.leaf { hyp := 406, conc := 369, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 406, conc := 402, proof := sorry })
                      (RArray.leaf { hyp := 4080, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4082, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4083, conc := 4064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4085, conc := 4079, proof := sorry })
                      (RArray.leaf { hyp := 4085, conc := 4082, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4088, conc := 4086, proof := sorry })
                      (RArray.leaf { hyp := 407, conc := 399, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4089, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4090, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4092, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4095, conc := 4066, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4095, conc := 4089, proof := sorry })
                      (RArray.leaf { hyp := 4095, conc := 4092, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4096, conc := 4066, proof := sorry })
                      (RArray.leaf { hyp := 4096, conc := 4090, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4096, conc := 4093, proof := sorry })
                      (RArray.leaf { hyp := 4097, conc := 4089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4097, conc := 4093, proof := sorry })
                      (RArray.leaf { hyp := 4098, conc := 4091, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4098, conc := 4096, proof := sorry })
                      (RArray.leaf { hyp := 408, conc := 393, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4099, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4099, conc := 4079, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4099, conc := 4089, proof := sorry })
                      (RArray.leaf { hyp := 4102, conc := 4081, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4102, conc := 4100, proof := sorry })
                      (RArray.leaf { hyp := 4102, conc := 4101, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4103, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4103, conc := 4082, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4103, conc := 4092, proof := sorry })
                      (RArray.leaf { hyp := 4104, conc := 4069, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4104, conc := 4083, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4104, conc := 4093, proof := sorry })
                      (RArray.leaf { hyp := 4105, conc := 4070, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4105, conc := 4082, proof := sorry })
                      (RArray.leaf { hyp := 4105, conc := 4093, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4106, conc := 4071, proof := sorry })
                      (RArray.leaf { hyp := 4106, conc := 4084, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4106, conc := 4103, proof := sorry })
                      (RArray.leaf { hyp := 4106, conc := 4104, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4106, conc := 4105, proof := sorry })
                      (RArray.leaf { hyp := 4107, conc := 4072, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4107, conc := 4079, proof := sorry })
                      (RArray.leaf { hyp := 4108, conc := 4072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4108, conc := 4080, proof := sorry })
                      (RArray.leaf { hyp := 4108, conc := 4093, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 409, conc := 392, proof := sorry })
                      (RArray.leaf { hyp := 409, conc := 396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 409, conc := 400, proof := sorry })
                      (RArray.leaf { hyp := 409, conc := 405, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 409, conc := 407, proof := sorry })
                      (RArray.leaf { hyp := 4109, conc := 4073, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4109, conc := 4079, proof := sorry })
                      (RArray.leaf { hyp := 4110, conc := 4081, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4111, conc := 4075, proof := sorry })
                      (RArray.leaf { hyp := 4111, conc := 4085, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4111, conc := 4099, proof := sorry })
                      (RArray.leaf { hyp := 4111, conc := 4103, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4111, conc := 4107, proof := sorry })
                      (RArray.leaf { hyp := 4112, conc := 4075, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4112, conc := 4086, proof := sorry })
                      (RArray.leaf { hyp := 4112, conc := 4096, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4112, conc := 4100, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4112, conc := 4104, proof := sorry })
                      (RArray.leaf { hyp := 4112, conc := 4108, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4113, conc := 4076, proof := sorry })
                      (RArray.leaf { hyp := 4113, conc := 4085, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4113, conc := 4101, proof := sorry })
                      (RArray.leaf { hyp := 4113, conc := 4105, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4113, conc := 4109, proof := sorry })
                      (RArray.leaf { hyp := 4114, conc := 4087, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4114, conc := 4099, proof := sorry })
                      (RArray.leaf { hyp := 4114, conc := 4104, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4115, conc := 4078, proof := sorry })
                      (RArray.leaf { hyp := 4115, conc := 4088, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4115, conc := 4102, proof := sorry })
                      (RArray.leaf { hyp := 4115, conc := 4106, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4117, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4118, conc := 4116, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4119, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4120, conc := 4064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4122, conc := 4116, proof := sorry })
                      (RArray.leaf { hyp := 4124, conc := 4116, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4125, conc := 4118, proof := sorry })
                      (RArray.leaf { hyp := 4125, conc := 4121, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4125, conc := 4123, proof := sorry })
                      (RArray.leaf { hyp := 4126, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4127, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 411, conc := 410, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4129, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4130, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4132, conc := 4129, proof := sorry })
                      (RArray.leaf { hyp := 4133, conc := 4066, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4133, conc := 4127, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4133, conc := 4130, proof := sorry })
                      (RArray.leaf { hyp := 4134, conc := 4067, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4134, conc := 4126, proof := sorry })
                      (RArray.leaf { hyp := 4134, conc := 4130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4135, conc := 4128, proof := sorry })
                      (RArray.leaf { hyp := 4135, conc := 4131, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4137, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4137, conc := 4117, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4137, conc := 4127, proof := sorry })
                      (RArray.leaf { hyp := 4138, conc := 4116, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 412, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4139, conc := 4118, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4139, conc := 4128, proof := sorry })
                      (RArray.leaf { hyp := 4139, conc := 4138, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4141, conc := 4120, proof := sorry })
                      (RArray.leaf { hyp := 4142, conc := 4070, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4142, conc := 4119, proof := sorry })
                      (RArray.leaf { hyp := 4143, conc := 4121, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4143, conc := 4131, proof := sorry })
                      (RArray.leaf { hyp := 4143, conc := 4141, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4143, conc := 4142, proof := sorry })
                      (RArray.leaf { hyp := 4145, conc := 4072, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4145, conc := 4117, proof := sorry })
                      (RArray.leaf { hyp := 4145, conc := 4130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4147, conc := 4131, proof := sorry })
                      (RArray.leaf { hyp := 4147, conc := 4144, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4147, conc := 4146, proof := sorry })
                      (RArray.leaf { hyp := 4148, conc := 4140, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4148, conc := 4144, proof := sorry })
                      (RArray.leaf { hyp := 413, conc := 410, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4149, conc := 4075, proof := sorry })
                      (RArray.leaf { hyp := 4149, conc := 4133, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4149, conc := 4137, proof := sorry })
                      (RArray.leaf { hyp := 4149, conc := 4141, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4149, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 4150, conc := 4122, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4150, conc := 4133, proof := sorry })
                      (RArray.leaf { hyp := 4150, conc := 4146, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4151, conc := 4124, proof := sorry })
                      (RArray.leaf { hyp := 4151, conc := 4134, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4152, conc := 4135, proof := sorry })
                      (RArray.leaf { hyp := 4152, conc := 4143, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4152, conc := 4147, proof := sorry })
                      (RArray.leaf { hyp := 4153, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4154, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4156, conc := 4064, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4157, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 414, conc := 411, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 414, conc := 412, proof := sorry })
                      (RArray.leaf { hyp := 414, conc := 413, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4161, conc := 4153, proof := sorry })
                      (RArray.leaf { hyp := 4161, conc := 4157, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4162, conc := 4155, proof := sorry })
                      (RArray.leaf { hyp := 4162, conc := 4158, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4163, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 4164, conc := 4064, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4166, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 415, conc := 410, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4170, conc := 4167, proof := sorry })
                      (RArray.leaf { hyp := 4172, conc := 4165, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4174, conc := 4069, proof := sorry })
                      (RArray.leaf { hyp := 4174, conc := 4154, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4174, conc := 4164, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 416, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4180, conc := 4158, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4181, conc := 4153, proof := sorry })
                      (RArray.leaf { hyp := 4181, conc := 4166, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4185, conc := 4159, proof := sorry })
                      (RArray.leaf { hyp := 4185, conc := 4169, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4185, conc := 4173, proof := sorry })
                      (RArray.leaf { hyp := 4186, conc := 4170, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4186, conc := 4178, proof := sorry })
                      (RArray.leaf { hyp := 4186, conc := 4182, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4187, conc := 4183, proof := sorry })
                      (RArray.leaf { hyp := 417, conc := 415, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 417, conc := 416, proof := sorry })
                      (RArray.leaf { hyp := 4189, conc := 4162, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4189, conc := 4180, proof := sorry })
                      (RArray.leaf { hyp := 4191, conc := 4079, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4191, conc := 4154, proof := sorry })
                      (RArray.leaf { hyp := 4193, conc := 4192, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4198, conc := 4156, proof := sorry })
                      (RArray.leaf { hyp := 418, conc := 410, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 37, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 38, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 39, proof := sorry })
                      (RArray.leaf { hyp := 4199, conc := 4082, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4199, conc := 4117, proof := sorry })
                      (RArray.leaf { hyp := 4199, conc := 4157, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4202, conc := 4190, proof := sorry })
                      (RArray.leaf { hyp := 4202, conc := 4194, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4202, conc := 4198, proof := sorry })
                      (RArray.leaf { hyp := 4203, conc := 4160, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4203, conc := 4191, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4203, conc := 4195, proof := sorry })
                      (RArray.leaf { hyp := 4205, conc := 4200, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4206, conc := 4197, proof := sorry })
                      (RArray.leaf { hyp := 4206, conc := 4204, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4207, conc := 4163, proof := sorry })
                      (RArray.leaf { hyp := 4208, conc := 4079, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4208, conc := 4164, proof := sorry })
                      (RArray.leaf { hyp := 419, conc := 410, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4210, conc := 4207, proof := sorry })
                      (RArray.leaf { hyp := 4214, conc := 4131, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4214, conc := 4211, proof := sorry })
                      (RArray.leaf { hyp := 4214, conc := 4213, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4215, conc := 4126, proof := sorry })
                      (RArray.leaf { hyp := 420, conc := 419, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4219, conc := 4207, proof := sorry })
                      (RArray.leaf { hyp := 4220, conc := 4212, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4220, conc := 4216, proof := sorry })
                      (RArray.leaf { hyp := 4222, conc := 4217, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4223, conc := 4172, proof := sorry })
                      (RArray.leaf { hyp := 4225, conc := 4089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4225, conc := 4117, proof := sorry })
                      (RArray.leaf { hyp := 4225, conc := 4164, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4228, conc := 4119, proof := sorry })
                      (RArray.leaf { hyp := 4228, conc := 4166, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 421, conc := 412, proof := sorry })
                      (RArray.leaf { hyp := 421, conc := 415, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 421, conc := 418, proof := sorry })
                      (RArray.leaf { hyp := 4231, conc := 4230, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4235, conc := 4168, proof := sorry })
                      (RArray.leaf { hyp := 4235, conc := 4234, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4236, conc := 4224, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4236, conc := 4232, proof := sorry })
                      (RArray.leaf { hyp := 4237, conc := 4229, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4237, conc := 4233, proof := sorry })
                      (RArray.leaf { hyp := 4238, conc := 4226, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4238, conc := 4234, proof := sorry })
                      (RArray.leaf { hyp := 4239, conc := 4171, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4239, conc := 4234, proof := sorry })
                      (RArray.leaf { hyp := 4240, conc := 4227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4240, conc := 4231, proof := sorry })
                      (RArray.leaf { hyp := 4240, conc := 4239, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4241, conc := 4207, proof := sorry })
                      (RArray.leaf { hyp := 4242, conc := 4137, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4242, conc := 4174, proof := sorry })
                      (RArray.leaf { hyp := 4242, conc := 4191, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4242, conc := 4208, proof := sorry })
                      (RArray.leaf { hyp := 4242, conc := 4225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4244, conc := 4226, proof := sorry })
                      (RArray.leaf { hyp := 4245, conc := 4176, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4245, conc := 4210, proof := sorry })
                      (RArray.leaf { hyp := 4245, conc := 4243, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4246, conc := 4177, proof := sorry })
                      (RArray.leaf { hyp := 4246, conc := 4228, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4247, conc := 4195, proof := sorry })
                      (RArray.leaf { hyp := 4248, conc := 4196, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4249, conc := 4179, proof := sorry })
                      (RArray.leaf { hyp := 4249, conc := 4230, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4250, conc := 4102, proof := sorry })
                      (RArray.leaf { hyp := 4250, conc := 4248, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4251, conc := 4198, proof := sorry })
                      (RArray.leaf { hyp := 4252, conc := 4199, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4253, conc := 4200, proof := sorry })
                      (RArray.leaf { hyp := 4254, conc := 4198, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4254, conc := 4234, proof := sorry })
                      (RArray.leaf { hyp := 4255, conc := 4180, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4255, conc := 4201, proof := sorry })
                      (RArray.leaf { hyp := 4255, conc := 4218, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4255, conc := 4251, proof := sorry })
                      (RArray.leaf { hyp := 4256, conc := 4211, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4258, conc := 4234, proof := sorry })
                      (RArray.leaf { hyp := 424, conc := 414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 424, conc := 417, proof := sorry })
                      (RArray.leaf { hyp := 424, conc := 420, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 424, conc := 421, proof := sorry })
                      (RArray.leaf { hyp := 424, conc := 422, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4259, conc := 4234, proof := sorry })
                      (RArray.leaf { hyp := 4260, conc := 4184, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4260, conc := 4193, proof := sorry })
                      (RArray.leaf { hyp := 4260, conc := 4214, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4261, conc := 4185, proof := sorry })
                      (RArray.leaf { hyp := 4261, conc := 4202, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4261, conc := 4251, proof := sorry })
                      (RArray.leaf { hyp := 4262, conc := 4186, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4262, conc := 4220, proof := sorry })
                      (RArray.leaf { hyp := 4262, conc := 4237, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4262, conc := 4242, proof := sorry })
                      (RArray.leaf { hyp := 4262, conc := 4247, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4262, conc := 4252, proof := sorry })
                      (RArray.leaf { hyp := 4262, conc := 4257, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4263, conc := 4204, proof := sorry })
                      (RArray.leaf { hyp := 4263, conc := 4221, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4263, conc := 4243, proof := sorry })
                      (RArray.leaf { hyp := 4264, conc := 4187, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4264, conc := 4202, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4264, conc := 4244, proof := sorry })
                      (RArray.leaf { hyp := 4265, conc := 4188, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4265, conc := 4205, proof := sorry })
                      (RArray.leaf { hyp := 4265, conc := 4222, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4266, conc := 4189, proof := sorry })
                      (RArray.leaf { hyp := 4266, conc := 4223, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 425, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4276, conc := 4275, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4278, conc := 4275, proof := sorry })
                      (RArray.leaf { hyp := 426, conc := 410, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4279, conc := 4269, proof := sorry })
                      (RArray.leaf { hyp := 4279, conc := 4275, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4280, conc := 4270, proof := sorry })
                      (RArray.leaf { hyp := 4280, conc := 4273, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4280, conc := 4276, proof := sorry })
                      (RArray.leaf { hyp := 4281, conc := 4267, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4285, conc := 4268, proof := sorry })
                      (RArray.leaf { hyp := 4285, conc := 4282, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4287, conc := 4269, proof := sorry })
                      (RArray.leaf { hyp := 4287, conc := 4283, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 426, proof := sorry })
                      (RArray.leaf { hyp := 4295, conc := 4268, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4295, conc := 4290, proof := sorry })
                      (RArray.leaf { hyp := 4296, conc := 4269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4296, conc := 4289, proof := sorry })
                      (RArray.leaf { hyp := 428, conc := 410, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 41, conc := 37, proof := sorry })
                      (RArray.leaf { hyp := 4301, conc := 4291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4301, conc := 4300, proof := sorry })
                      (RArray.leaf { hyp := 4303, conc := 4271, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4303, conc := 4283, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4304, conc := 4272, proof := sorry })
                      (RArray.leaf { hyp := 4304, conc := 4282, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4305, conc := 4273, proof := sorry })
                      (RArray.leaf { hyp := 4306, conc := 4274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4307, conc := 4276, proof := sorry })
                      (RArray.leaf { hyp := 4307, conc := 4281, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4307, conc := 4293, proof := sorry })
                      (RArray.leaf { hyp := 4307, conc := 4306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4308, conc := 4298, proof := sorry })
                      (RArray.leaf { hyp := 4310, conc := 4278, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4310, conc := 4285, proof := sorry })
                      (RArray.leaf { hyp := 4310, conc := 4295, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4310, conc := 4300, proof := sorry })
                      (RArray.leaf { hyp := 4310, conc := 4304, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4311, conc := 4298, proof := sorry })
                      (RArray.leaf { hyp := 4312, conc := 4280, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4312, conc := 4288, proof := sorry })
                      (RArray.leaf { hyp := 4314, conc := 4313, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4315, conc := 4268, proof := sorry })
                      (RArray.leaf { hyp := 4317, conc := 4269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4317, conc := 4313, proof := sorry })
                      (RArray.leaf { hyp := 4318, conc := 4317, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4324, conc := 4269, proof := sorry })
                      (RArray.leaf { hyp := 4324, conc := 4319, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4325, conc := 4321, proof := sorry })
                      (RArray.leaf { hyp := 4326, conc := 4271, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4326, conc := 4319, proof := sorry })
                      (RArray.leaf { hyp := 4327, conc := 4320, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4328, conc := 4321, proof := sorry })
                      (RArray.leaf { hyp := 431, conc := 412, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 431, conc := 425, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 431, conc := 428, proof := sorry })
                      (RArray.leaf { hyp := 4329, conc := 4271, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4330, conc := 4313, proof := sorry })
                      (RArray.leaf { hyp := 4331, conc := 4272, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4333, conc := 4322, proof := sorry })
                      (RArray.leaf { hyp := 4333, conc := 4326, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4333, conc := 4329, proof := sorry })
                      (RArray.leaf { hyp := 4334, conc := 4277, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4334, conc := 4327, proof := sorry })
                      (RArray.leaf { hyp := 4334, conc := 4330, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4335, conc := 4278, proof := sorry })
                      (RArray.leaf { hyp := 4335, conc := 4315, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4335, conc := 4323, proof := sorry })
                      (RArray.leaf { hyp := 4335, conc := 4331, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4336, conc := 4317, proof := sorry })
                      (RArray.leaf { hyp := 4336, conc := 4324, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4336, conc := 4326, proof := sorry })
                      (RArray.leaf { hyp := 4336, conc := 4330, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4337, conc := 4325, proof := sorry })
                      (RArray.leaf { hyp := 4337, conc := 4334, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4338, conc := 4267, proof := sorry })
                      (RArray.leaf { hyp := 432, conc := 426, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4339, conc := 4268, proof := sorry })
                      (RArray.leaf { hyp := 4340, conc := 4269, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4341, conc := 4339, proof := sorry })
                      (RArray.leaf { hyp := 4344, conc := 4342, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4346, conc := 4343, proof := sorry })
                      (RArray.leaf { hyp := 4348, conc := 4273, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4348, conc := 4347, proof := sorry })
                      (RArray.leaf { hyp := 433, conc := 429, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4350, conc := 4271, proof := sorry })
                      (RArray.leaf { hyp := 4351, conc := 4349, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4352, conc := 4349, proof := sorry })
                      (RArray.leaf { hyp := 4353, conc := 4347, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4354, conc := 4279, proof := sorry })
                      (RArray.leaf { hyp := 4354, conc := 4340, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4354, conc := 4345, proof := sorry })
                      (RArray.leaf { hyp := 4354, conc := 4350, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4355, conc := 4346, proof := sorry })
                      (RArray.leaf { hyp := 4355, conc := 4348, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4355, conc := 4352, proof := sorry })
                      (RArray.leaf { hyp := 4356, conc := 4314, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4356, conc := 4338, proof := sorry })
                      (RArray.leaf { hyp := 4357, conc := 4282, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4358, conc := 4284, proof := sorry })
                      (RArray.leaf { hyp := 4358, conc := 4338, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4358, conc := 4357, proof := sorry })
                      (RArray.leaf { hyp := 434, conc := 414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 434, conc := 430, proof := sorry })
                      (RArray.leaf { hyp := 4359, conc := 4286, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4360, conc := 4288, proof := sorry })
                      (RArray.leaf { hyp := 4360, conc := 4318, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4360, conc := 4341, proof := sorry })
                      (RArray.leaf { hyp := 4360, conc := 4358, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4361, conc := 4319, proof := sorry })
                      (RArray.leaf { hyp := 4362, conc := 4343, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4363, conc := 4282, proof := sorry })
                      (RArray.leaf { hyp := 4363, conc := 4319, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4365, conc := 4363, proof := sorry })
                      (RArray.leaf { hyp := 4366, conc := 4286, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4366, conc := 4322, proof := sorry })
                      (RArray.leaf { hyp := 4366, conc := 4361, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4367, conc := 4346, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4367, conc := 4365, proof := sorry })
                      (RArray.leaf { hyp := 4368, conc := 4289, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 435, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4369, conc := 4291, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4370, conc := 4344, proof := sorry })
                      (RArray.leaf { hyp := 4370, conc := 4368, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4372, conc := 4318, proof := sorry })
                      (RArray.leaf { hyp := 4372, conc := 4369, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4372, conc := 4370, proof := sorry })
                      (RArray.leaf { hyp := 4373, conc := 4329, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4374, conc := 4301, proof := sorry })
                      (RArray.leaf { hyp := 4374, conc := 4332, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4374, conc := 4351, proof := sorry })
                      (RArray.leaf { hyp := 4375, conc := 4327, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4375, conc := 4357, proof := sorry })
                      (RArray.leaf { hyp := 4376, conc := 4328, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4377, conc := 4333, proof := sorry })
                      (RArray.leaf { hyp := 4377, conc := 4366, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4378, conc := 4337, proof := sorry })
                      (RArray.leaf { hyp := 4378, conc := 4372, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 436, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4380, conc := 4379, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4381, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4382, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4383, conc := 4380, proof := sorry })
                      (RArray.leaf { hyp := 4383, conc := 4381, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4383, conc := 4382, proof := sorry })
                      (RArray.leaf { hyp := 4384, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4385, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4387, conc := 4379, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4388, conc := 4379, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4389, conc := 4380, proof := sorry })
                      (RArray.leaf { hyp := 4389, conc := 4387, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4389, conc := 4388, proof := sorry })
                      (RArray.leaf { hyp := 4390, conc := 4381, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4390, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4390, conc := 4387, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4391, conc := 4381, proof := sorry })
                      (RArray.leaf { hyp := 4391, conc := 4385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4391, conc := 4388, proof := sorry })
                      (RArray.leaf { hyp := 4392, conc := 4382, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4392, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4392, conc := 4388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4393, conc := 4386, proof := sorry })
                      (RArray.leaf { hyp := 4394, conc := 4379, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4395, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4396, conc := 4380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4396, conc := 4394, proof := sorry })
                      (RArray.leaf { hyp := 4396, conc := 4395, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4397, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4398, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 438, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4399, conc := 4380, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4399, conc := 4397, proof := sorry })
                      (RArray.leaf { hyp := 4399, conc := 4398, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4400, conc := 4381, proof := sorry })
                      (RArray.leaf { hyp := 4400, conc := 4394, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4400, conc := 4397, proof := sorry })
                      (RArray.leaf { hyp := 4401, conc := 4381, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4401, conc := 4395, proof := sorry })
                      (RArray.leaf { hyp := 4401, conc := 4398, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4402, conc := 4382, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4402, conc := 4394, proof := sorry })
                      (RArray.leaf { hyp := 4402, conc := 4398, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4403, conc := 4383, proof := sorry })
                      (RArray.leaf { hyp := 4403, conc := 4396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4403, conc := 4399, proof := sorry })
                      (RArray.leaf { hyp := 4403, conc := 4400, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4403, conc := 4401, proof := sorry })
                      (RArray.leaf { hyp := 4403, conc := 4402, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4404, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4405, conc := 4379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4407, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4408, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 439, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4411, conc := 4381, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4411, conc := 4405, proof := sorry })
                      (RArray.leaf { hyp := 4411, conc := 4408, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4412, conc := 4382, proof := sorry })
                      (RArray.leaf { hyp := 4412, conc := 4404, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4412, conc := 4408, proof := sorry })
                      (RArray.leaf { hyp := 4414, conc := 4384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4414, conc := 4394, proof := sorry })
                      (RArray.leaf { hyp := 4414, conc := 4404, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4415, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4415, conc := 4395, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4415, conc := 4405, proof := sorry })
                      (RArray.leaf { hyp := 4417, conc := 4386, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4417, conc := 4406, proof := sorry })
                      (RArray.leaf { hyp := 4417, conc := 4416, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4419, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4419, conc := 4398, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4419, conc := 4408, proof := sorry })
                      (RArray.leaf { hyp := 4420, conc := 4385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4420, conc := 4397, proof := sorry })
                      (RArray.leaf { hyp := 4420, conc := 4408, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4421, conc := 4409, proof := sorry })
                      (RArray.leaf { hyp := 4421, conc := 4418, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4422, conc := 4387, proof := sorry })
                      (RArray.leaf { hyp := 4422, conc := 4394, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4422, conc := 4407, proof := sorry })
                      (RArray.leaf { hyp := 4423, conc := 4387, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4423, conc := 4395, proof := sorry })
                      (RArray.leaf { hyp := 4423, conc := 4408, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4424, conc := 4388, proof := sorry })
                      (RArray.leaf { hyp := 4424, conc := 4394, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4424, conc := 4408, proof := sorry })
                      (RArray.leaf { hyp := 4425, conc := 4389, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4425, conc := 4396, proof := sorry })
                      (RArray.leaf { hyp := 4425, conc := 4409, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4425, conc := 4422, proof := sorry })
                      (RArray.leaf { hyp := 4425, conc := 4423, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4425, conc := 4424, proof := sorry })
                      (RArray.leaf { hyp := 4426, conc := 4390, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4426, conc := 4400, proof := sorry })
                      (RArray.leaf { hyp := 4426, conc := 4410, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4426, conc := 4414, proof := sorry })
                      (RArray.leaf { hyp := 4426, conc := 4418, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4426, conc := 4422, proof := sorry })
                      (RArray.leaf { hyp := 4427, conc := 4390, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4427, conc := 4401, proof := sorry })
                      (RArray.leaf { hyp := 4427, conc := 4411, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4427, conc := 4415, proof := sorry })
                      (RArray.leaf { hyp := 4427, conc := 4419, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4427, conc := 4423, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4428, conc := 4391, proof := sorry })
                      (RArray.leaf { hyp := 4428, conc := 4400, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4428, conc := 4411, proof := sorry })
                      (RArray.leaf { hyp := 4428, conc := 4416, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4428, conc := 4420, proof := sorry })
                      (RArray.leaf { hyp := 4428, conc := 4424, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 441, conc := 435, proof := sorry })
                      (RArray.leaf { hyp := 441, conc := 438, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4429, conc := 4392, proof := sorry })
                      (RArray.leaf { hyp := 4429, conc := 4402, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4429, conc := 4412, proof := sorry })
                      (RArray.leaf { hyp := 4429, conc := 4414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4429, conc := 4419, proof := sorry })
                      (RArray.leaf { hyp := 4429, conc := 4424, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4430, conc := 4403, proof := sorry })
                      (RArray.leaf { hyp := 4430, conc := 4413, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4430, conc := 4417, proof := sorry })
                      (RArray.leaf { hyp := 4430, conc := 4427, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4430, conc := 4429, proof := sorry })
                      (RArray.leaf { hyp := 4431, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4432, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4433, conc := 4380, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4433, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4433, conc := 4432, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4434, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4435, conc := 4379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4436, conc := 4380, proof := sorry })
                      (RArray.leaf { hyp := 4436, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4436, conc := 4435, proof := sorry })
                      (RArray.leaf { hyp := 4437, conc := 4381, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4437, conc := 4431, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4437, conc := 4434, proof := sorry })
                      (RArray.leaf { hyp := 4438, conc := 4381, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4438, conc := 4432, proof := sorry })
                      (RArray.leaf { hyp := 4438, conc := 4435, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 442, conc := 412, proof := sorry })
                      (RArray.leaf { hyp := 442, conc := 436, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 442, conc := 439, proof := sorry })
                      (RArray.leaf { hyp := 4439, conc := 4382, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4439, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4439, conc := 4435, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4440, conc := 4383, proof := sorry })
                      (RArray.leaf { hyp := 4440, conc := 4433, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4440, conc := 4436, proof := sorry })
                      (RArray.leaf { hyp := 4440, conc := 4437, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4440, conc := 4438, proof := sorry })
                      (RArray.leaf { hyp := 4440, conc := 4439, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4441, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4442, conc := 4379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4444, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4445, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 443, conc := 413, proof := sorry })
                      (RArray.leaf { hyp := 443, conc := 435, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 443, conc := 439, proof := sorry })
                      (RArray.leaf { hyp := 4449, conc := 4382, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4449, conc := 4441, proof := sorry })
                      (RArray.leaf { hyp := 4449, conc := 4445, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4450, conc := 4447, proof := sorry })
                      (RArray.leaf { hyp := 4451, conc := 4384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4451, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4451, conc := 4441, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4453, conc := 4442, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4454, conc := 4386, proof := sorry })
                      (RArray.leaf { hyp := 4454, conc := 4443, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4454, conc := 4453, proof := sorry })
                      (RArray.leaf { hyp := 4455, conc := 4384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4455, conc := 4434, proof := sorry })
                      (RArray.leaf { hyp := 4455, conc := 4444, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4457, conc := 4385, proof := sorry })
                      (RArray.leaf { hyp := 4457, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4457, conc := 4445, proof := sorry })
                      (RArray.leaf { hyp := 4458, conc := 4446, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4458, conc := 4456, proof := sorry })
                      (RArray.leaf { hyp := 444, conc := 437, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 444, conc := 440, proof := sorry })
                      (RArray.leaf { hyp := 4459, conc := 4387, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4459, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4459, conc := 4444, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4460, conc := 4387, proof := sorry })
                      (RArray.leaf { hyp := 4460, conc := 4432, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4460, conc := 4445, proof := sorry })
                      (RArray.leaf { hyp := 4461, conc := 4388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4461, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4461, conc := 4445, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4462, conc := 4389, proof := sorry })
                      (RArray.leaf { hyp := 4462, conc := 4433, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4462, conc := 4446, proof := sorry })
                      (RArray.leaf { hyp := 4462, conc := 4459, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4462, conc := 4460, proof := sorry })
                      (RArray.leaf { hyp := 4462, conc := 4461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4463, conc := 4447, proof := sorry })
                      (RArray.leaf { hyp := 4464, conc := 4452, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4465, conc := 4391, proof := sorry })
                      (RArray.leaf { hyp := 4465, conc := 4437, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4465, conc := 4448, proof := sorry })
                      (RArray.leaf { hyp := 4465, conc := 4453, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4465, conc := 4457, proof := sorry })
                      (RArray.leaf { hyp := 4465, conc := 4461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4466, conc := 4392, proof := sorry })
                      (RArray.leaf { hyp := 4466, conc := 4439, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4466, conc := 4449, proof := sorry })
                      (RArray.leaf { hyp := 4466, conc := 4451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4466, conc := 4456, proof := sorry })
                      (RArray.leaf { hyp := 4466, conc := 4461, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4467, conc := 4440, proof := sorry })
                      (RArray.leaf { hyp := 4467, conc := 4450, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4467, conc := 4454, proof := sorry })
                      (RArray.leaf { hyp := 4468, conc := 4379, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4469, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4470, conc := 4380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4470, conc := 4468, proof := sorry })
                      (RArray.leaf { hyp := 4470, conc := 4469, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4471, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4472, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4473, conc := 4380, proof := sorry })
                      (RArray.leaf { hyp := 4473, conc := 4471, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4473, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 4474, conc := 4381, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4474, conc := 4468, proof := sorry })
                      (RArray.leaf { hyp := 4474, conc := 4471, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4475, conc := 4381, proof := sorry })
                      (RArray.leaf { hyp := 4475, conc := 4469, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4475, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 4476, conc := 4382, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4476, conc := 4468, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4476, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 4477, conc := 4383, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4477, conc := 4470, proof := sorry })
                      (RArray.leaf { hyp := 4477, conc := 4473, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4477, conc := 4474, proof := sorry })
                      (RArray.leaf { hyp := 4477, conc := 4475, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4477, conc := 4476, proof := sorry })
                      (RArray.leaf { hyp := 4478, conc := 4379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4479, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4481, conc := 4379, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4482, conc := 4379, proof := sorry })
                      (RArray.leaf { hyp := 4485, conc := 4381, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4485, conc := 4479, proof := sorry })
                      (RArray.leaf { hyp := 4485, conc := 4482, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4487, conc := 4480, proof := sorry })
                      (RArray.leaf { hyp := 4488, conc := 4384, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4488, conc := 4468, proof := sorry })
                      (RArray.leaf { hyp := 4488, conc := 4478, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4489, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4489, conc := 4469, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4489, conc := 4479, proof := sorry })
                      (RArray.leaf { hyp := 4490, conc := 4385, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4490, conc := 4468, proof := sorry })
                      (RArray.leaf { hyp := 4490, conc := 4479, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4491, conc := 4386, proof := sorry })
                      (RArray.leaf { hyp := 4491, conc := 4470, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4493, conc := 4384, proof := sorry })
                      (RArray.leaf { hyp := 4493, conc := 4472, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4493, conc := 4482, proof := sorry })
                      (RArray.leaf { hyp := 4495, conc := 4386, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4495, conc := 4483, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4495, conc := 4492, proof := sorry })
                      (RArray.leaf { hyp := 4495, conc := 4494, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4496, conc := 4387, proof := sorry })
                      (RArray.leaf { hyp := 4496, conc := 4468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4496, conc := 4481, proof := sorry })
                      (RArray.leaf { hyp := 4497, conc := 4387, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4497, conc := 4469, proof := sorry })
                      (RArray.leaf { hyp := 4497, conc := 4482, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4498, conc := 4388, proof := sorry })
                      (RArray.leaf { hyp := 4498, conc := 4468, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4498, conc := 4482, proof := sorry })
                      (RArray.leaf { hyp := 448, conc := 446, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4499, conc := 4389, proof := sorry })
                      (RArray.leaf { hyp := 4499, conc := 4470, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4499, conc := 4483, proof := sorry })
                      (RArray.leaf { hyp := 4499, conc := 4496, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4499, conc := 4497, proof := sorry })
                      (RArray.leaf { hyp := 4499, conc := 4498, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4500, conc := 4390, proof := sorry })
                      (RArray.leaf { hyp := 4500, conc := 4474, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4500, conc := 4488, proof := sorry })
                      (RArray.leaf { hyp := 4500, conc := 4492, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4500, conc := 4496, proof := sorry })
                      (RArray.leaf { hyp := 4501, conc := 4390, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4501, conc := 4475, proof := sorry })
                      (RArray.leaf { hyp := 4501, conc := 4485, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4501, conc := 4489, proof := sorry })
                      (RArray.leaf { hyp := 4501, conc := 4493, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4501, conc := 4497, proof := sorry })
                      (RArray.leaf { hyp := 4502, conc := 4391, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4502, conc := 4474, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4502, conc := 4485, proof := sorry })
                      (RArray.leaf { hyp := 4502, conc := 4490, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4502, conc := 4494, proof := sorry })
                      (RArray.leaf { hyp := 4502, conc := 4498, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4503, conc := 4392, proof := sorry })
                      (RArray.leaf { hyp := 4503, conc := 4476, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4503, conc := 4486, proof := sorry })
                      (RArray.leaf { hyp := 4503, conc := 4488, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4503, conc := 4493, proof := sorry })
                      (RArray.leaf { hyp := 4503, conc := 4498, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4504, conc := 4477, proof := sorry })
                      (RArray.leaf { hyp := 4504, conc := 4491, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4504, conc := 4495, proof := sorry })
                      (RArray.leaf { hyp := 4505, conc := 4394, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4505, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4505, conc := 4468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4506, conc := 4394, proof := sorry })
                      (RArray.leaf { hyp := 4506, conc := 4432, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4506, conc := 4469, proof := sorry })
                      (RArray.leaf { hyp := 4507, conc := 4395, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4507, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4507, conc := 4469, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4508, conc := 4396, proof := sorry })
                      (RArray.leaf { hyp := 4508, conc := 4433, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4508, conc := 4470, proof := sorry })
                      (RArray.leaf { hyp := 4508, conc := 4505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4508, conc := 4506, proof := sorry })
                      (RArray.leaf { hyp := 4508, conc := 4507, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 449, conc := 415, proof := sorry })
                      (RArray.leaf { hyp := 449, conc := 438, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4509, conc := 4394, proof := sorry })
                      (RArray.leaf { hyp := 4509, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4509, conc := 4471, proof := sorry })
                      (RArray.leaf { hyp := 4510, conc := 4394, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4510, conc := 4435, proof := sorry })
                      (RArray.leaf { hyp := 4510, conc := 4472, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4511, conc := 4395, proof := sorry })
                      (RArray.leaf { hyp := 4511, conc := 4434, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4511, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 4512, conc := 4396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4512, conc := 4436, proof := sorry })
                      (RArray.leaf { hyp := 4512, conc := 4473, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4512, conc := 4509, proof := sorry })
                      (RArray.leaf { hyp := 4512, conc := 4510, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4512, conc := 4511, proof := sorry })
                      (RArray.leaf { hyp := 4514, conc := 4397, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4514, conc := 4432, proof := sorry })
                      (RArray.leaf { hyp := 4514, conc := 4472, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4515, conc := 4398, proof := sorry })
                      (RArray.leaf { hyp := 4515, conc := 4431, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4515, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 4517, conc := 4400, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4517, conc := 4437, proof := sorry })
                      (RArray.leaf { hyp := 4517, conc := 4474, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4517, conc := 4505, proof := sorry })
                      (RArray.leaf { hyp := 4517, conc := 4509, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4517, conc := 4513, proof := sorry })
                      (RArray.leaf { hyp := 4518, conc := 4400, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4518, conc := 4438, proof := sorry })
                      (RArray.leaf { hyp := 4518, conc := 4475, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4518, conc := 4506, proof := sorry })
                      (RArray.leaf { hyp := 4518, conc := 4510, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4518, conc := 4514, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4519, conc := 4401, proof := sorry })
                      (RArray.leaf { hyp := 4519, conc := 4437, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4519, conc := 4475, proof := sorry })
                      (RArray.leaf { hyp := 4519, conc := 4507, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4519, conc := 4511, proof := sorry })
                      (RArray.leaf { hyp := 4519, conc := 4515, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4520, conc := 4402, proof := sorry })
                      (RArray.leaf { hyp := 4520, conc := 4439, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4520, conc := 4476, proof := sorry })
                      (RArray.leaf { hyp := 4520, conc := 4505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4520, conc := 4510, proof := sorry })
                      (RArray.leaf { hyp := 4520, conc := 4515, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4521, conc := 4516, proof := sorry })
                      (RArray.leaf { hyp := 4524, conc := 4395, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4524, conc := 4441, proof := sorry })
                      (RArray.leaf { hyp := 4524, conc := 4479, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4528, conc := 4395, proof := sorry })
                      (RArray.leaf { hyp := 4528, conc := 4444, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4528, conc := 4482, proof := sorry })
                      (RArray.leaf { hyp := 451, conc := 416, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 451, conc := 428, proof := sorry })
                      (RArray.leaf { hyp := 451, conc := 439, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4529, conc := 4446, proof := sorry })
                      (RArray.leaf { hyp := 4530, conc := 4397, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4530, conc := 4441, proof := sorry })
                      (RArray.leaf { hyp := 4530, conc := 4481, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4532, conc := 4398, proof := sorry })
                      (RArray.leaf { hyp := 4532, conc := 4441, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4532, conc := 4482, proof := sorry })
                      (RArray.leaf { hyp := 4534, conc := 4530, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4535, conc := 4523, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4536, conc := 4447, proof := sorry })
                      (RArray.leaf { hyp := 4538, conc := 4525, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4538, conc := 4533, proof := sorry })
                      (RArray.leaf { hyp := 452, conc := 450, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4540, conc := 4404, proof := sorry })
                      (RArray.leaf { hyp := 4540, conc := 4432, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4540, conc := 4479, proof := sorry })
                      (RArray.leaf { hyp := 4541, conc := 4405, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4541, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4541, conc := 4479, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4543, conc := 4404, proof := sorry })
                      (RArray.leaf { hyp := 4543, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4543, conc := 4481, proof := sorry })
                      (RArray.leaf { hyp := 4544, conc := 4435, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4545, conc := 4405, proof := sorry })
                      (RArray.leaf { hyp := 4545, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4545, conc := 4482, proof := sorry })
                      (RArray.leaf { hyp := 4549, conc := 4408, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4549, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 4549, conc := 4482, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4550, conc := 4409, proof := sorry })
                      (RArray.leaf { hyp := 4550, conc := 4483, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4550, conc := 4547, proof := sorry })
                      (RArray.leaf { hyp := 4551, conc := 4543, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4553, conc := 4411, proof := sorry })
                      (RArray.leaf { hyp := 4553, conc := 4437, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4553, conc := 4485, proof := sorry })
                      (RArray.leaf { hyp := 4553, conc := 4541, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4553, conc := 4545, proof := sorry })
                      (RArray.leaf { hyp := 4553, conc := 4549, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4555, conc := 4542, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4555, conc := 4546, proof := sorry })
                      (RArray.leaf { hyp := 4555, conc := 4552, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4556, conc := 4414, proof := sorry })
                      (RArray.leaf { hyp := 4556, conc := 4451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4556, conc := 4488, proof := sorry })
                      (RArray.leaf { hyp := 4556, conc := 4505, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4556, conc := 4522, proof := sorry })
                      (RArray.leaf { hyp := 4557, conc := 4540, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4558, conc := 4415, proof := sorry })
                      (RArray.leaf { hyp := 4558, conc := 4451, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4558, conc := 4489, proof := sorry })
                      (RArray.leaf { hyp := 4558, conc := 4507, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4558, conc := 4524, proof := sorry })
                      (RArray.leaf { hyp := 4558, conc := 4541, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 454, conc := 418, proof := sorry })
                      (RArray.leaf { hyp := 454, conc := 426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4559, conc := 4523, proof := sorry })
                      (RArray.leaf { hyp := 4560, conc := 4417, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4560, conc := 4508, proof := sorry })
                      (RArray.leaf { hyp := 4560, conc := 4557, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4561, conc := 4455, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4414, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4562, conc := 4456, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4510, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4562, conc := 4527, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4544, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4563, conc := 4415, proof := sorry })
                      (RArray.leaf { hyp := 4563, conc := 4455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4563, conc := 4493, proof := sorry })
                      (RArray.leaf { hyp := 4563, conc := 4511, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4563, conc := 4528, proof := sorry })
                      (RArray.leaf { hyp := 4563, conc := 4545, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4565, conc := 4546, proof := sorry })
                      (RArray.leaf { hyp := 4565, conc := 4561, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4568, conc := 4419, proof := sorry })
                      (RArray.leaf { hyp := 4568, conc := 4451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4568, conc := 4493, proof := sorry })
                      (RArray.leaf { hyp := 4568, conc := 4515, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4568, conc := 4532, proof := sorry })
                      (RArray.leaf { hyp := 4568, conc := 4549, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4569, conc := 4494, proof := sorry })
                      (RArray.leaf { hyp := 4569, conc := 4513, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4569, conc := 4531, proof := sorry })
                      (RArray.leaf { hyp := 4570, conc := 4533, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4571, conc := 4422, proof := sorry })
                      (RArray.leaf { hyp := 4571, conc := 4459, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4571, conc := 4496, proof := sorry })
                      (RArray.leaf { hyp := 4571, conc := 4505, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4571, conc := 4547, proof := sorry })
                      (RArray.leaf { hyp := 4572, conc := 4527, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4572, conc := 4548, proof := sorry })
                      (RArray.leaf { hyp := 4573, conc := 4423, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4573, conc := 4459, proof := sorry })
                      (RArray.leaf { hyp := 4573, conc := 4497, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4573, conc := 4507, proof := sorry })
                      (RArray.leaf { hyp := 4573, conc := 4528, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4573, conc := 4549, proof := sorry })
                      (RArray.leaf { hyp := 4574, conc := 4424, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4574, conc := 4461, proof := sorry })
                      (RArray.leaf { hyp := 4574, conc := 4498, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4574, conc := 4505, proof := sorry })
                      (RArray.leaf { hyp := 4574, conc := 4527, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4574, conc := 4549, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4575, conc := 4508, proof := sorry })
                      (RArray.leaf { hyp := 4575, conc := 4529, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4575, conc := 4550, proof := sorry })
                      (RArray.leaf { hyp := 4575, conc := 4572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4575, conc := 4573, proof := sorry })
                      (RArray.leaf { hyp := 4576, conc := 4426, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4576, conc := 4463, proof := sorry })
                      (RArray.leaf { hyp := 4576, conc := 4500, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4576, conc := 4517, proof := sorry })
                      (RArray.leaf { hyp := 4576, conc := 4534, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4576, conc := 4551, proof := sorry })
                      (RArray.leaf { hyp := 4576, conc := 4556, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4576, conc := 4571, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4426, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4577, conc := 4464, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4518, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4577, conc := 4535, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4552, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4577, conc := 4562, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4578, conc := 4427, proof := sorry })
                      (RArray.leaf { hyp := 4578, conc := 4536, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4578, conc := 4553, proof := sorry })
                      (RArray.leaf { hyp := 4578, conc := 4563, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4578, conc := 4568, proof := sorry })
                      (RArray.leaf { hyp := 456, conc := 453, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 456, conc := 455, proof := sorry })
                      (RArray.leaf { hyp := 4579, conc := 4535, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4579, conc := 4564, proof := sorry })
                      (RArray.leaf { hyp := 4579, conc := 4569, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4580, conc := 4520, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4580, conc := 4554, proof := sorry })
                      (RArray.leaf { hyp := 4580, conc := 4562, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4581, conc := 4538, proof := sorry })
                      (RArray.leaf { hyp := 4581, conc := 4560, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 457, conc := 421, proof := sorry })
                      (RArray.leaf { hyp := 457, conc := 449, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 457, conc := 453, proof := sorry })
                      (RArray.leaf { hyp := 4591, conc := 4589, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4591, conc := 4590, proof := sorry })
                      (RArray.leaf { hyp := 4593, conc := 4590, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4594, conc := 4584, proof := sorry })
                      (RArray.leaf { hyp := 4594, conc := 4590, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4595, conc := 4593, proof := sorry })
                      (RArray.leaf { hyp := 4596, conc := 4582, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 458, conc := 446, proof := sorry })
                      (RArray.leaf { hyp := 458, conc := 454, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 44, conc := 38, proof := sorry })
                      (RArray.leaf { hyp := 4600, conc := 4583, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4600, conc := 4597, proof := sorry })
                      (RArray.leaf { hyp := 4601, conc := 4598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4602, conc := 4584, proof := sorry })
                      (RArray.leaf { hyp := 4602, conc := 4598, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4608, conc := 4582, proof := sorry })
                      (RArray.leaf { hyp := 4608, conc := 4607, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 459, conc := 455, proof := sorry })
                      (RArray.leaf { hyp := 4609, conc := 4607, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4610, conc := 4583, proof := sorry })
                      (RArray.leaf { hyp := 4610, conc := 4605, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4611, conc := 4584, proof := sorry })
                      (RArray.leaf { hyp := 4611, conc := 4604, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4612, conc := 4606, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4616, conc := 4588, proof := sorry })
                      (RArray.leaf { hyp := 4616, conc := 4613, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4618, conc := 4586, proof := sorry })
                      (RArray.leaf { hyp := 4618, conc := 4598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 460, conc := 450, proof := sorry })
                      (RArray.leaf { hyp := 4619, conc := 4587, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4619, conc := 4597, proof := sorry })
                      (RArray.leaf { hyp := 4620, conc := 4588, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4621, conc := 4589, proof := sorry })
                      (RArray.leaf { hyp := 4622, conc := 4591, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4622, conc := 4608, proof := sorry })
                      (RArray.leaf { hyp := 4623, conc := 4592, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4623, conc := 4613, proof := sorry })
                      (RArray.leaf { hyp := 4624, conc := 4621, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4625, conc := 4593, proof := sorry })
                      (RArray.leaf { hyp := 4625, conc := 4600, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4625, conc := 4610, proof := sorry })
                      (RArray.leaf { hyp := 4625, conc := 4615, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4625, conc := 4619, proof := sorry })
                      (RArray.leaf { hyp := 4626, conc := 4594, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4626, conc := 4602, proof := sorry })
                      (RArray.leaf { hyp := 4626, conc := 4611, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4626, conc := 4613, proof := sorry })
                      (RArray.leaf { hyp := 4626, conc := 4618, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4627, conc := 4595, proof := sorry })
                      (RArray.leaf { hyp := 4627, conc := 4603, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4627, conc := 4620, proof := sorry })
                      (RArray.leaf { hyp := 4627, conc := 4623, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 461, conc := 434, proof := sorry })
                      (RArray.leaf { hyp := 461, conc := 448, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 461, conc := 452, proof := sorry })
                      (RArray.leaf { hyp := 461, conc := 456, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4629, conc := 4628, proof := sorry })
                      (RArray.leaf { hyp := 4630, conc := 4583, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4631, conc := 4628, proof := sorry })
                      (RArray.leaf { hyp := 4632, conc := 4584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4632, conc := 4628, proof := sorry })
                      (RArray.leaf { hyp := 4633, conc := 4632, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4636, conc := 4635, proof := sorry })
                      (RArray.leaf { hyp := 4639, conc := 4584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4639, conc := 4634, proof := sorry })
                      (RArray.leaf { hyp := 4641, conc := 4586, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4641, conc := 4634, proof := sorry })
                      (RArray.leaf { hyp := 4644, conc := 4586, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4645, conc := 4628, proof := sorry })
                      (RArray.leaf { hyp := 4646, conc := 4587, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4648, conc := 4637, proof := sorry })
                      (RArray.leaf { hyp := 4648, conc := 4644, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 463, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4649, conc := 4645, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4650, conc := 4593, proof := sorry })
                      (RArray.leaf { hyp := 4650, conc := 4630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4650, conc := 4638, proof := sorry })
                      (RArray.leaf { hyp := 4650, conc := 4646, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4651, conc := 4594, proof := sorry })
                      (RArray.leaf { hyp := 4651, conc := 4632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4651, conc := 4639, proof := sorry })
                      (RArray.leaf { hyp := 4651, conc := 4641, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4651, conc := 4645, proof := sorry })
                      (RArray.leaf { hyp := 4652, conc := 4649, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4655, conc := 4584, proof := sorry })
                      (RArray.leaf { hyp := 4656, conc := 4654, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4658, conc := 4657, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4659, conc := 4657, proof := sorry })
                      (RArray.leaf { hyp := 4665, conc := 4586, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4666, conc := 4664, proof := sorry })
                      (RArray.leaf { hyp := 4667, conc := 4592, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 465, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 4669, conc := 4594, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4669, conc := 4655, proof := sorry })
                      (RArray.leaf { hyp := 4669, conc := 4660, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4669, conc := 4665, proof := sorry })
                      (RArray.leaf { hyp := 4670, conc := 4595, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4671, conc := 4596, proof := sorry })
                      (RArray.leaf { hyp := 4671, conc := 4629, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4671, conc := 4653, proof := sorry })
                      (RArray.leaf { hyp := 4672, conc := 4597, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4673, conc := 4599, proof := sorry })
                      (RArray.leaf { hyp := 4673, conc := 4653, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4673, conc := 4672, proof := sorry })
                      (RArray.leaf { hyp := 4674, conc := 4601, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4674, conc := 4630, proof := sorry })
                      (RArray.leaf { hyp := 4674, conc := 4654, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4675, conc := 4603, proof := sorry })
                      (RArray.leaf { hyp := 4675, conc := 4633, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4675, conc := 4656, proof := sorry })
                      (RArray.leaf { hyp := 4675, conc := 4673, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4676, conc := 4634, proof := sorry })
                      (RArray.leaf { hyp := 4677, conc := 4636, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4677, conc := 4658, proof := sorry })
                      (RArray.leaf { hyp := 4677, conc := 4676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4678, conc := 4597, proof := sorry })
                      (RArray.leaf { hyp := 4678, conc := 4634, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 466, conc := 410, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4680, conc := 4637, proof := sorry })
                      (RArray.leaf { hyp := 4680, conc := 4678, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4681, conc := 4601, proof := sorry })
                      (RArray.leaf { hyp := 4681, conc := 4637, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4681, conc := 4676, proof := sorry })
                      (RArray.leaf { hyp := 4682, conc := 4680, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4683, conc := 4604, proof := sorry })
                      (RArray.leaf { hyp := 4684, conc := 4606, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4685, conc := 4609, proof := sorry })
                      (RArray.leaf { hyp := 4685, conc := 4659, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4685, conc := 4683, proof := sorry })
                      (RArray.leaf { hyp := 4687, conc := 4612, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4687, conc := 4633, proof := sorry })
                      (RArray.leaf { hyp := 4687, conc := 4685, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4687, conc := 4686, proof := sorry })
                      (RArray.leaf { hyp := 4688, conc := 4644, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4689, conc := 4616, proof := sorry })
                      (RArray.leaf { hyp := 4689, conc := 4647, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4689, conc := 4666, proof := sorry })
                      (RArray.leaf { hyp := 4689, conc := 4684, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4690, conc := 4642, proof := sorry })
                      (RArray.leaf { hyp := 4691, conc := 4643, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4692, conc := 4624, proof := sorry })
                      (RArray.leaf { hyp := 4692, conc := 4648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4692, conc := 4668, proof := sorry })
                      (RArray.leaf { hyp := 4692, conc := 4681, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4693, conc := 4627, proof := sorry })
                      (RArray.leaf { hyp := 4693, conc := 4682, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4693, conc := 4687, proof := sorry })
                      (RArray.leaf { hyp := 45, conc := 40, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 45, conc := 43, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 471, conc := 464, proof := sorry })
                      (RArray.leaf { hyp := 471, conc := 470, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 472, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 474, conc := 473, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 475, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 476, conc := 410, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 478, conc := 475, proof := sorry })
                      (RArray.leaf { hyp := 480, conc := 413, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 480, conc := 472, proof := sorry })
                      (RArray.leaf { hyp := 480, conc := 476, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 481, conc := 474, proof := sorry })
                      (RArray.leaf { hyp := 482, conc := 462, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 485, conc := 474, proof := sorry })
                      (RArray.leaf { hyp := 485, conc := 484, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 488, conc := 416, proof := sorry })
                      (RArray.leaf { hyp := 488, conc := 465, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 47, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 491, conc := 463, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 493, conc := 477, proof := sorry })
                      (RArray.leaf { hyp := 494, conc := 468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 494, conc := 478, proof := sorry })
                      (RArray.leaf { hyp := 495, conc := 479, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 496, conc := 479, proof := sorry })
                      (RArray.leaf { hyp := 497, conc := 487, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 497, conc := 492, proof := sorry })
                      (RArray.leaf { hyp := 498, conc := 424, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 498, conc := 485, proof := sorry })
                      (RArray.leaf { hyp := 498, conc := 496, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 500, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 502, conc := 410, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 503, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 508, conc := 501, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 508, conc := 504, proof := sorry })
                      (RArray.leaf { hyp := 508, conc := 506, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 508, conc := 507, proof := sorry })
                      (RArray.leaf { hyp := 49, conc := 46, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 510, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 512, conc := 410, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 518, conc := 514, proof := sorry })
                      (RArray.leaf { hyp := 518, conc := 516, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 518, conc := 517, proof := sorry })
                      (RArray.leaf { hyp := 50, conc := 47, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 522, conc := 501, proof := sorry })
                      (RArray.leaf { hyp := 522, conc := 511, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 522, conc := 520, proof := sorry })
                      (RArray.leaf { hyp := 523, conc := 502, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 524, conc := 513, proof := sorry })
                      (RArray.leaf { hyp := 526, conc := 525, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 527, conc := 418, proof := sorry })
                      (RArray.leaf { hyp := 527, conc := 499, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 527, conc := 512, proof := sorry })
                      (RArray.leaf { hyp := 528, conc := 500, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 530, conc := 528, proof := sorry })
                      (RArray.leaf { hyp := 530, conc := 529, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 531, conc := 523, proof := sorry })
                      (RArray.leaf { hyp := 532, conc := 520, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 535, conc := 508, proof := sorry })
                      (RArray.leaf { hyp := 535, conc := 526, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 535, conc := 530, proof := sorry })
                      (RArray.leaf { hyp := 535, conc := 532, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 535, conc := 533, proof := sorry })
                      (RArray.leaf { hyp := 535, conc := 534, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 52, conc := 46, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 539, conc := 464, proof := sorry })
                      (RArray.leaf { hyp := 539, conc := 538, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 541, conc := 466, proof := sorry })
                      (RArray.leaf { hyp := 543, conc := 467, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 543, conc := 541, proof := sorry })
                      (RArray.leaf { hyp := 545, conc := 463, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 547, conc := 546, proof := sorry })
                      (RArray.leaf { hyp := 548, conc := 544, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 549, conc := 506, proof := sorry })
                      (RArray.leaf { hyp := 550, conc := 546, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 551, conc := 546, proof := sorry })
                      (RArray.leaf { hyp := 552, conc := 547, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 552, conc := 549, proof := sorry })
                      (RArray.leaf { hyp := 552, conc := 550, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 552, conc := 551, proof := sorry })
                      (RArray.leaf { hyp := 553, conc := 509, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 426, proof := sorry })
                      (RArray.leaf { hyp := 556, conc := 474, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 54, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 560, conc := 558, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 560, conc := 559, proof := sorry })
                      (RArray.leaf { hyp := 561, conc := 428, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 561, conc := 472, proof := sorry })
                      (RArray.leaf { hyp := 561, conc := 512, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 562, conc := 473, proof := sorry })
                      (RArray.leaf { hyp := 564, conc := 474, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 564, conc := 563, proof := sorry })
                      (RArray.leaf { hyp := 565, conc := 478, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 55, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 569, conc := 564, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 569, conc := 566, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 569, conc := 567, proof := sorry })
                      (RArray.leaf { hyp := 569, conc := 568, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 573, conc := 464, proof := sorry })
                      (RArray.leaf { hyp := 573, conc := 572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 574, conc := 435, proof := sorry })
                      (RArray.leaf { hyp := 574, conc := 465, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 577, conc := 575, proof := sorry })
                      (RArray.leaf { hyp := 577, conc := 576, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 580, conc := 513, proof := sorry })
                      (RArray.leaf { hyp := 581, conc := 579, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 581, conc := 580, proof := sorry })
                      (RArray.leaf { hyp := 582, conc := 515, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 582, conc := 570, proof := sorry })
                      (RArray.leaf { hyp := 582, conc := 578, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 583, conc := 575, proof := sorry })
                      (RArray.leaf { hyp := 585, conc := 580, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 586, conc := 581, proof := sorry })
                      (RArray.leaf { hyp := 586, conc := 583, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 586, conc := 584, proof := sorry })
                      (RArray.leaf { hyp := 586, conc := 585, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 587, conc := 536, proof := sorry })
                      (RArray.leaf { hyp := 587, conc := 553, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 588, conc := 483, proof := sorry })
                      (RArray.leaf { hyp := 588, conc := 520, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 57, conc := 48, proof := sorry })
                      (RArray.leaf { hyp := 589, conc := 520, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 590, conc := 447, proof := sorry })
                      (RArray.leaf { hyp := 590, conc := 484, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 591, conc := 485, proof := sorry })
                      (RArray.leaf { hyp := 591, conc := 522, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 591, conc := 539, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 591, conc := 556, proof := sorry })
                      (RArray.leaf { hyp := 591, conc := 573, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 591, conc := 589, proof := sorry })
                      (RArray.leaf { hyp := 591, conc := 590, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 592, conc := 445, proof := sorry })
                      (RArray.leaf { hyp := 592, conc := 574, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 596, conc := 543, proof := sorry })
                      (RArray.leaf { hyp := 596, conc := 593, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 596, conc := 594, proof := sorry })
                      (RArray.leaf { hyp := 596, conc := 595, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 597, conc := 482, proof := sorry })
                      (RArray.leaf { hyp := 597, conc := 561, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 598, conc := 524, proof := sorry })
                      (RArray.leaf { hyp := 598, conc := 562, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 598, conc := 579, proof := sorry })
                      (RArray.leaf { hyp := 58, conc := 52, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 599, conc := 580, proof := sorry })
                      (RArray.leaf { hyp := 600, conc := 580, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 601, conc := 599, proof := sorry })
                      (RArray.leaf { hyp := 601, conc := 600, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 602, conc := 490, proof := sorry })
                      (RArray.leaf { hyp := 602, conc := 536, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 602, conc := 557, proof := sorry })
                      (RArray.leaf { hyp := 604, conc := 580, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 605, conc := 580, proof := sorry })
                      (RArray.leaf { hyp := 606, conc := 603, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 606, conc := 604, proof := sorry })
                      (RArray.leaf { hyp := 606, conc := 605, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 607, conc := 494, proof := sorry })
                      (RArray.leaf { hyp := 607, conc := 531, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 607, conc := 548, proof := sorry })
                      (RArray.leaf { hyp := 607, conc := 565, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 607, conc := 592, proof := sorry })
                      (RArray.leaf { hyp := 610, conc := 605, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 611, conc := 460, proof := sorry })
                      (RArray.leaf { hyp := 612, conc := 601, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 612, conc := 606, proof := sorry })
                      (RArray.leaf { hyp := 612, conc := 608, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 612, conc := 609, proof := sorry })
                      (RArray.leaf { hyp := 612, conc := 610, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 612, conc := 611, proof := sorry })
                      (RArray.leaf { hyp := 614, conc := 613, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 615, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 616, conc := 613, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 617, conc := 615, proof := sorry })
                      (RArray.leaf { hyp := 617, conc := 616, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 618, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 60, conc := 53, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 60, conc := 58, proof := sorry })
                      (RArray.leaf { hyp := 60, conc := 59, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 619, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 620, conc := 614, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 620, conc := 619, proof := sorry })
                      (RArray.leaf { hyp := 621, conc := 613, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 622, conc := 613, proof := sorry })
                      (RArray.leaf { hyp := 623, conc := 614, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 623, conc := 621, proof := sorry })
                      (RArray.leaf { hyp := 623, conc := 622, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 624, conc := 615, proof := sorry })
                      (RArray.leaf { hyp := 624, conc := 618, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 624, conc := 621, proof := sorry })
                      (RArray.leaf { hyp := 625, conc := 615, proof := sorry })))))))))))

end EndToEnd
