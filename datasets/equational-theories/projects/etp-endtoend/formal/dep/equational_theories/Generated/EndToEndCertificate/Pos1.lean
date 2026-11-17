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
def _root_.EndToEnd.pos1 : RArray EndToEnd.PosFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3678, conc := 3700, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3680, conc := 3706, proof := sorry })
                      (RArray.leaf { hyp := 3681, conc := 3708, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3682, conc := 3696, proof := sorry })
                      (RArray.leaf { hyp := 3685, conc := 3692, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3688, conc := 3692, proof := sorry })
                      (RArray.leaf { hyp := 3689, conc := 3676, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3690, conc := 3692, proof := sorry })
                      (RArray.leaf { hyp := 3694, conc := 3706, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3695, conc := 3707, proof := sorry })
                      (RArray.leaf { hyp := 3696, conc := 3709, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3697, conc := 3683, proof := sorry })
                      (RArray.leaf { hyp := 3698, conc := 3708, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 368, conc := 4622, proof := sorry })
                      (RArray.leaf { hyp := 3699, conc := 39, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3703, conc := 3708, proof := sorry })
                      (RArray.leaf { hyp := 3710, conc := 4152, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3714, conc := 4469, proof := sorry })
                      (RArray.leaf { hyp := 3715, conc := 326, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3715, conc := 3920, proof := sorry })
                      (RArray.leaf { hyp := 3715, conc := 4506, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3717, conc := 328, proof := sorry })
                      (RArray.leaf { hyp := 3717, conc := 3934, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3717, conc := 4507, proof := sorry })
                      (RArray.leaf { hyp := 3726, conc := 3725, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 371, conc := 4626, proof := sorry })
                      (RArray.leaf { hyp := 3734, conc := 3737, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3735, conc := 3524, proof := sorry })
                      (RArray.leaf { hyp := 3735, conc := 380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3735, conc := 4475, proof := sorry })
                      (RArray.leaf { hyp := 3736, conc := 3322, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3736, conc := 3942, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3737, conc := 4518, proof := sorry })
                      (RArray.leaf { hyp := 3739, conc := 3333, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3739, conc := 3536, proof := sorry })
                      (RArray.leaf { hyp := 3739, conc := 3942, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3739, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 3739, conc := 4511, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3743, conc := 4519, proof := sorry })
                      (RArray.leaf { hyp := 3749, conc := 3357, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3750, conc := 3721, proof := sorry })
                      (RArray.leaf { hyp := 3750, conc := 3723, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3750, conc := 3748, proof := sorry })
                      (RArray.leaf { hyp := 3750, conc := 42, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3752, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3753, conc := 40, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3754, conc := 3797, proof := sorry })
                      (RArray.leaf { hyp := 3755, conc := 3819, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3757, conc := 331, proof := sorry })
                      (RArray.leaf { hyp := 3759, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3763, conc := 3766, proof := sorry })
                      (RArray.leaf { hyp := 3763, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3767, conc := 3835, proof := sorry })
                      (RArray.leaf { hyp := 3767, conc := 40, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3768, conc := 3785, proof := sorry })
                      (RArray.leaf { hyp := 3769, conc := 3488, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3769, conc := 4209, proof := sorry })
                      (RArray.leaf { hyp := 3770, conc := 3839, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3771, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 3775, conc := 3619, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3775, conc := 4683, proof := sorry })
                      (RArray.leaf { hyp := 3779, conc := 3855, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3788, conc := 40, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3789, conc := 3532, proof := sorry })
                      (RArray.leaf { hyp := 3789, conc := 394, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3789, conc := 4489, proof := sorry })
                      (RArray.leaf { hyp := 3790, conc := 3972, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3790, conc := 4175, proof := sorry })
                      (RArray.leaf { hyp := 3790, conc := 4304, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3793, conc := 3536, proof := sorry })
                      (RArray.leaf { hyp := 3793, conc := 4225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3797, conc := 4558, proof := sorry })
                      (RArray.leaf { hyp := 3801, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3803, conc := 4196, proof := sorry })
                      (RArray.leaf { hyp := 3805, conc := 4194, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 3296, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 3397, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 3736, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 3822, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 3894, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 4006, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 4296, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 4368, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 4619, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 4672, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3813, conc := 3817, proof := sorry })
                      (RArray.leaf { hyp := 3822, conc := 3728, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 383, conc := 3455, proof := sorry })
                      (RArray.leaf { hyp := 383, conc := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 383, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3861, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3868, conc := 3871, proof := sorry })
                      (RArray.leaf { hyp := 3873, conc := 358, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3873, conc := 3659, proof := sorry })
                      (RArray.leaf { hyp := 3873, conc := 4067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3874, conc := 3871, proof := sorry })
                      (RArray.leaf { hyp := 3878, conc := 3907, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 386, conc := 3341, proof := sorry })
                      (RArray.leaf { hyp := 386, conc := 3544, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 386, conc := 3757, proof := sorry })
                      (RArray.leaf { hyp := 386, conc := 3963, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 386, conc := 4342, proof := sorry })
                      (RArray.leaf { hyp := 386, conc := 4469, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 386, conc := 4607, proof := sorry })
                      (RArray.leaf { hyp := 3881, conc := 3903, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3883, conc := 3897, proof := sorry })
                      (RArray.leaf { hyp := 3884, conc := 3911, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3885, conc := 3899, proof := sorry })
                      (RArray.leaf { hyp := 3888, conc := 3895, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3890, conc := 3905, proof := sorry })
                      (RArray.leaf { hyp := 3891, conc := 3871, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3891, conc := 3904, proof := sorry })
                      (RArray.leaf { hyp := 3891, conc := 3906, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3891, conc := 3907, proof := sorry })
                      (RArray.leaf { hyp := 3891, conc := 4096, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3893, conc := 3905, proof := sorry })
                      (RArray.leaf { hyp := 3894, conc := 3905, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3895, conc := 3906, proof := sorry })
                      (RArray.leaf { hyp := 3897, conc := 3872, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3897, conc := 3893, proof := sorry })
                      (RArray.leaf { hyp := 3897, conc := 3901, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3897, conc := 3909, proof := sorry })
                      (RArray.leaf { hyp := 3898, conc := 3910, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3899, conc := 3912, proof := sorry })
                      (RArray.leaf { hyp := 3901, conc := 3905, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3902, conc := 3905, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3905, conc := 39, proof := sorry })
                      (RArray.leaf { hyp := 3906, conc := 3891, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3906, conc := 3905, proof := sorry })
                      (RArray.leaf { hyp := 3909, conc := 3692, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3918, conc := 322, proof := sorry })
                      (RArray.leaf { hyp := 3918, conc := 3512, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3918, conc := 378, proof := sorry })
                      (RArray.leaf { hyp := 3918, conc := 4399, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3925, conc := 324, proof := sorry })
                      (RArray.leaf { hyp := 3925, conc := 3519, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3925, conc := 378, proof := sorry })
                      (RArray.leaf { hyp := 3925, conc := 4436, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3928, conc := 325, proof := sorry })
                      (RArray.leaf { hyp := 3928, conc := 3522, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3928, conc := 378, proof := sorry })
                      (RArray.leaf { hyp := 3928, conc := 4473, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3929, conc := 3722, proof := sorry })
                      (RArray.leaf { hyp := 3929, conc := 376, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3929, conc := 4509, proof := sorry })
                      (RArray.leaf { hyp := 3931, conc := 3728, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3932, conc := 4512, proof := sorry })
                      (RArray.leaf { hyp := 3937, conc := 382, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 3330, proof := sorry })
                      (RArray.leaf { hyp := 3939, conc := 3525, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 3736, proof := sorry })
                      (RArray.leaf { hyp := 3939, conc := 3739, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 3931, proof := sorry })
                      (RArray.leaf { hyp := 3939, conc := 4142, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 4357, proof := sorry })
                      (RArray.leaf { hyp := 3939, conc := 4476, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3939, conc := 4514, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3956, conc := 3970, proof := sorry })
                      (RArray.leaf { hyp := 3958, conc := 3330, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3958, conc := 3775, proof := sorry })
                      (RArray.leaf { hyp := 3958, conc := 4199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3958, conc := 4368, proof := sorry })
                      (RArray.leaf { hyp := 3958, conc := 4457, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3966, conc := 3560, proof := sorry })
                      (RArray.leaf { hyp := 3970, conc := 3346, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3972, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 3972, conc := 3413, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3972, conc := 4022, proof := sorry })
                      (RArray.leaf { hyp := 3972, conc := 4306, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3972, conc := 4683, proof := sorry })
                      (RArray.leaf { hyp := 3974, conc := 3970, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3975, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 3978, conc := 3572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3979, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 3989, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3991, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 398, conc := 44, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4004, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4006, conc := 3413, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4008, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4009, conc := 44, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4012, conc := 4215, proof := sorry })
                      (RArray.leaf { hyp := 4013, conc := 44, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4023, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4025, conc := 4181, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4026, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 4030, conc := 44, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4044, conc := 44, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4049, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 4054, conc := 44, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4064, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4071, conc := 4068, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4074, conc := 4068, proof := sorry })
                      (RArray.leaf { hyp := 4077, conc := 4068, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4079, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 4081, conc := 4074, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4081, conc := 4107, proof := sorry })
                      (RArray.leaf { hyp := 4081, conc := 4108, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4081, conc := 4109, proof := sorry })
                      (RArray.leaf { hyp := 4081, conc := 4110, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4084, conc := 4106, proof := sorry })
                      (RArray.leaf { hyp := 4085, conc := 4095, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4086, conc := 4112, proof := sorry })
                      (RArray.leaf { hyp := 4087, conc := 4077, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4087, conc := 4109, proof := sorry })
                      (RArray.leaf { hyp := 4087, conc := 4114, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4088, conc := 4115, proof := sorry })
                      (RArray.leaf { hyp := 4091, conc := 368, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4093, conc := 4097, proof := sorry })
                      (RArray.leaf { hyp := 4094, conc := 4098, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4095, conc := 366, proof := sorry })
                      (RArray.leaf { hyp := 4096, conc := 368, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4100, conc := 4112, proof := sorry })
                      (RArray.leaf { hyp := 4101, conc := 4113, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4102, conc := 4111, proof := sorry })
                      (RArray.leaf { hyp := 4102, conc := 4113, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4102, conc := 4114, proof := sorry })
                      (RArray.leaf { hyp := 4102, conc := 4115, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4109, conc := 4098, proof := sorry })
                      (RArray.leaf { hyp := 410, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4121, conc := 4125, proof := sorry })
                      (RArray.leaf { hyp := 4121, conc := 4152, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4125, conc := 4078, proof := sorry })
                      (RArray.leaf { hyp := 4125, conc := 4147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 411, conc := 2, proof := sorry })
                      (RArray.leaf { hyp := 4131, conc := 4671, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4132, conc := 4135, proof := sorry })
                      (RArray.leaf { hyp := 4139, conc := 4152, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4140, conc := 4152, proof := sorry })
                      (RArray.leaf { hyp := 4142, conc := 4672, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4148, conc := 41, proof := sorry })
                      (RArray.leaf { hyp := 413, conc := 3658, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4150, conc := 4148, proof := sorry })
                      (RArray.leaf { hyp := 4151, conc := 4152, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4153, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 4155, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4158, conc := 4155, proof := sorry })
                      (RArray.leaf { hyp := 414, conc := 47, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4160, conc := 38, proof := sorry })
                      (RArray.leaf { hyp := 4169, conc := 4236, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4173, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3293, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 3384, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3403, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 3590, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3606, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 3702, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3803, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 3809, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3939, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 3958, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4105, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4161, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4215, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4228, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4363, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4412, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4420, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4449, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4460, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4490, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4540, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 4639, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4175, conc := 4678, proof := sorry })
                      (RArray.leaf { hyp := 4177, conc := 4194, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4178, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 4181, conc := 3552, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4182, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 4185, conc := 4261, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 417, conc := 1427, proof := sorry })
                      (RArray.leaf { hyp := 417, conc := 2242, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 417, conc := 3254, proof := sorry })
                      (RArray.leaf { hyp := 417, conc := 414, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 417, conc := 624, proof := sorry })
                      (RArray.leaf { hyp := 417, conc := 818, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4194, conc := 3347, proof := sorry })
                      (RArray.leaf { hyp := 4195, conc := 38, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4197, conc := 4206, proof := sorry })
                      (RArray.leaf { hyp := 4203, conc := 4262, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4207, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 4208, conc := 384, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 3600, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 3755, proof := sorry })
                      (RArray.leaf { hyp := 4209, conc := 3793, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 4108, proof := sorry })
                      (RArray.leaf { hyp := 4209, conc := 4324, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 4361, proof := sorry })
                      (RArray.leaf { hyp := 4209, conc := 4611, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 4683, proof := sorry })
                      (RArray.leaf { hyp := 4211, conc := 3749, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4212, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 4215, conc := 4012, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4216, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 420, conc := 4394, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 420, conc := 627, proof := sorry })
                      (RArray.leaf { hyp := 4219, conc := 4261, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4228, conc := 3322, proof := sorry })
                      (RArray.leaf { hyp := 4228, conc := 3536, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4228, conc := 3942, proof := sorry })
                      (RArray.leaf { hyp := 4228, conc := 4225, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4228, conc := 4496, proof := sorry })
                      (RArray.leaf { hyp := 4229, conc := 44, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4233, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 422, conc := 1021, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 422, conc := 3319, proof := sorry })
                      (RArray.leaf { hyp := 422, conc := 420, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4242, conc := 363, proof := sorry })
                      (RArray.leaf { hyp := 4242, conc := 394, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4242, conc := 4039, proof := sorry })
                      (RArray.leaf { hyp := 4242, conc := 4688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4246, conc := 4261, proof := sorry })
                      (RArray.leaf { hyp := 423, conc := 422, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4252, conc := 44, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4257, conc := 44, proof := sorry })
                      (RArray.leaf { hyp := 424, conc := 1020, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 424, conc := 1022, proof := sorry })
                      (RArray.leaf { hyp := 424, conc := 1629, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4267, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4268, conc := 0, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4269, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4271, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4272, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4274, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4275, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4276, conc := 4307, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 426, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 4282, conc := 0, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4283, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 101, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 1026, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 104, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1066, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 1228, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1231, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 1238, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1241, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 1248, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1639, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 1842, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 1848, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 2036, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 2252, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 2458, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 2648, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 2861, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 3461, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 3660, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 3720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 3724, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 376, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 3926, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 3927, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 4119, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 4120, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 4129, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 4285, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 4431, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 4471, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 4472, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 4597, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 4598, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 4628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 51, proof := sorry })
                      (RArray.leaf { hyp := 427, conc := 834, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 427, conc := 835, proof := sorry })
                      (RArray.leaf { hyp := 4289, conc := 0, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4290, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4292, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4298, conc := 4287, proof := sorry })
                      (RArray.leaf { hyp := 4298, conc := 4296, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4298, conc := 4303, proof := sorry })
                      (RArray.leaf { hyp := 4298, conc := 4307, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4298, conc := 4311, proof := sorry })
                      (RArray.leaf { hyp := 4298, conc := 4354, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4300, conc := 4310, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 429, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 4313, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 430, conc := 460, proof := sorry })
                      (RArray.leaf { hyp := 4319, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4320, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 431, conc := 377, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4330, conc := 4336, proof := sorry })
                      (RArray.leaf { hyp := 432, conc := 1066, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 432, conc := 853, proof := sorry })
                      (RArray.leaf { hyp := 4342, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4343, conc := 4364, proof := sorry })
                      (RArray.leaf { hyp := 433, conc := 1059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 433, conc := 1854, proof := sorry })
                      (RArray.leaf { hyp := 433, conc := 1862, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 433, conc := 359, proof := sorry })
                      (RArray.leaf { hyp := 433, conc := 442, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 433, conc := 839, proof := sorry })
                      (RArray.leaf { hyp := 4379, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4386, conc := 4383, proof := sorry })
                      (RArray.leaf { hyp := 4386, conc := 4389, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4386, conc := 4390, proof := sorry })
                      (RArray.leaf { hyp := 4386, conc := 4391, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4386, conc := 4392, proof := sorry })
                      (RArray.leaf { hyp := 4386, conc := 4393, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 437, conc := 461, proof := sorry })
                      (RArray.leaf { hyp := 438, conc := 358, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4406, conc := 4430, proof := sorry })
                      (RArray.leaf { hyp := 4410, conc := 4426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4416, conc := 4428, proof := sorry })
                      (RArray.leaf { hyp := 4418, conc := 4410, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 440, conc := 3, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 440, conc := 648, proof := sorry })
                      (RArray.leaf { hyp := 441, conc := 431, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4443, conc := 4464, proof := sorry })
                      (RArray.leaf { hyp := 4447, conc := 4390, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4447, conc := 4437, proof := sorry })
                      (RArray.leaf { hyp := 4447, conc := 4451, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4447, conc := 4455, proof := sorry })
                      (RArray.leaf { hyp := 4447, conc := 4459, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4447, conc := 4463, proof := sorry })
                      (RArray.leaf { hyp := 4448, conc := 4453, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 443, conc := 857, proof := sorry })
                      (RArray.leaf { hyp := 4452, conc := 4464, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4453, conc := 4465, proof := sorry })
                      (RArray.leaf { hyp := 4456, conc := 4439, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4456, conc := 4466, proof := sorry })
                      (RArray.leaf { hyp := 444, conc := 635, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4464, conc := 4440, proof := sorry })
                      (RArray.leaf { hyp := 4464, conc := 4467, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 445, conc := 441, proof := sorry })
                      (RArray.leaf { hyp := 445, conc := 457, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 446, conc := 459, proof := sorry })
                      (RArray.leaf { hyp := 4480, conc := 4504, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4484, conc := 4500, proof := sorry })
                      (RArray.leaf { hyp := 447, conc := 440, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4491, conc := 4504, proof := sorry })
                      (RArray.leaf { hyp := 4492, conc := 4484, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 448, conc := 630, proof := sorry })
                      (RArray.leaf { hyp := 449, conc := 431, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4513, conc := 4517, proof := sorry })
                      (RArray.leaf { hyp := 4516, conc := 4403, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4516, conc := 4440, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4516, conc := 4477, proof := sorry })
                      (RArray.leaf { hyp := 4516, conc := 4508, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4516, conc := 4512, proof := sorry })
                      (RArray.leaf { hyp := 4516, conc := 4517, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4516, conc := 4518, proof := sorry })
                      (RArray.leaf { hyp := 4516, conc := 4519, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4516, conc := 4520, proof := sorry })
                      (RArray.leaf { hyp := 4516, conc := 4521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 450, conc := 459, proof := sorry })
                      (RArray.leaf { hyp := 4522, conc := 4539, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4523, conc := 4364, proof := sorry })
                      (RArray.leaf { hyp := 4523, conc := 4531, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4525, conc := 4552, proof := sorry })
                      (RArray.leaf { hyp := 4526, conc := 4571, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4527, conc := 4574, proof := sorry })
                      (RArray.leaf { hyp := 4531, conc := 4559, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4531, conc := 4564, proof := sorry })
                      (RArray.leaf { hyp := 4534, conc := 4551, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4534, conc := 4576, proof := sorry })
                      (RArray.leaf { hyp := 4535, conc := 4579, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4536, conc := 4501, proof := sorry })
                      (RArray.leaf { hyp := 4536, conc := 4519, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4536, conc := 4558, proof := sorry })
                      (RArray.leaf { hyp := 4536, conc := 4573, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4536, conc := 4578, proof := sorry })
                      (RArray.leaf { hyp := 452, conc := 2084, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4539, conc := 4556, proof := sorry })
                      (RArray.leaf { hyp := 4542, conc := 4567, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4544, conc := 4364, proof := sorry })
                      (RArray.leaf { hyp := 4544, conc := 4537, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4547, conc := 4526, proof := sorry })
                      (RArray.leaf { hyp := 4548, conc := 4575, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 453, conc := 445, proof := sorry })
                      (RArray.leaf { hyp := 4551, conc := 4566, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4552, conc := 4567, proof := sorry })
                      (RArray.leaf { hyp := 4557, conc := 4567, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 454, conc := 1052, proof := sorry })
                      (RArray.leaf { hyp := 4559, conc := 4531, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4560, conc := 4521, proof := sorry })
                      (RArray.leaf { hyp := 4560, conc := 4565, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4561, conc := 4534, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4429, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4562, conc := 4466, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4562, conc := 4556, proof := sorry })
                      (RArray.leaf { hyp := 4562, conc := 4568, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4562, conc := 4574, proof := sorry })
                      (RArray.leaf { hyp := 4566, conc := 4561, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4567, conc := 4525, proof := sorry })
                      (RArray.leaf { hyp := 4567, conc := 4581, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 455, conc := 56, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4577, conc := 4467, proof := sorry })
                      (RArray.leaf { hyp := 4577, conc := 4504, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4577, conc := 4578, proof := sorry })
                      (RArray.leaf { hyp := 456, conc := 643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4583, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4584, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4587, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4589, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4590, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4596, conc := 0, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4597, conc := 0, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4598, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4604, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4605, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4607, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4613, conc := 4626, proof := sorry })
                      (RArray.leaf { hyp := 4615, conc := 4625, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4628, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 4634, conc := 0, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4635, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 462, conc := 490, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4642, conc := 4679, proof := sorry })
                      (RArray.leaf { hyp := 4645, conc := 4651, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 463, conc := 1831, proof := sorry })
                      (RArray.leaf { hyp := 463, conc := 22, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4657, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 464, conc := 2920, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4665, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 467, conc := 2906, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 468, conc := 602, proof := sorry })
                      (RArray.leaf { hyp := 469, conc := 3176, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 470, conc := 471, proof := sorry })
                      (RArray.leaf { hyp := 473, conc := 7, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 474, conc := 749, proof := sorry })
                      (RArray.leaf { hyp := 477, conc := 479, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 478, conc := 602, proof := sorry })
                      (RArray.leaf { hyp := 46, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 479, conc := 3195, proof := sorry })
                      (RArray.leaf { hyp := 480, conc := 1522, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 482, conc := 468, proof := sorry })
                      (RArray.leaf { hyp := 483, conc := 469, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 484, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 486, conc := 462, proof := sorry })
                      (RArray.leaf { hyp := 487, conc := 2787, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 488, conc := 1503, proof := sorry })
                      (RArray.leaf { hyp := 47, conc := 1426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 47, conc := 2239, proof := sorry })
                      (RArray.leaf { hyp := 47, conc := 3253, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 47, conc := 614, proof := sorry })
                      (RArray.leaf { hyp := 47, conc := 817, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 489, conc := 588, proof := sorry })
                      (RArray.leaf { hyp := 490, conc := 38, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 490, conc := 544, proof := sorry })
                      (RArray.leaf { hyp := 491, conc := 758, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 492, conc := 2990, proof := sorry })
                      (RArray.leaf { hyp := 493, conc := 1281, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 495, conc := 2712, proof := sorry })
                      (RArray.leaf { hyp := 497, conc := 1958, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 499, conc := 527, proof := sorry })
                      (RArray.leaf { hyp := 499, conc := 574, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 501, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 504, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 505, conc := 494, proof := sorry })
                      (RArray.leaf { hyp := 506, conc := 889, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 507, conc := 1745, proof := sorry })
                      (RArray.leaf { hyp := 507, conc := 1995, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 507, conc := 913, proof := sorry })
                      (RArray.leaf { hyp := 49, conc := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 509, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 509, conc := 438, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 511, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 515, conc := 602, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 50, conc := 8, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 519, conc := 486, proof := sorry })
                      (RArray.leaf { hyp := 520, conc := 2917, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 1164, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 1292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 1303, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 1373, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 1506, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 1560, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 1698, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 1942, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 2179, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 2195, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 2278, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 2334, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 2398, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 2924, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 3119, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 3416, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 4215, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 4304, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 4412, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 4420, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 521, conc := 4449, proof := sorry })
                      (RArray.leaf { hyp := 521, conc := 4639, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 523, conc := 607, proof := sorry })
                      (RArray.leaf { hyp := 527, conc := 4306, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 51, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 51, conc := 628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 536, conc := 582, proof := sorry })
                      (RArray.leaf { hyp := 537, conc := 2771, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 538, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 52, conc := 1037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 540, conc := 486, proof := sorry })
                      (RArray.leaf { hyp := 541, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 542, conc := 1963, proof := sorry })
                      (RArray.leaf { hyp := 544, conc := 607, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 545, conc := 1966, proof := sorry })
                      (RArray.leaf { hyp := 546, conc := 690, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 53, conc := 1432, proof := sorry })
                      (RArray.leaf { hyp := 53, conc := 630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 553, conc := 540, proof := sorry })
                      (RArray.leaf { hyp := 554, conc := 873, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 1116, proof := sorry })
                      (RArray.leaf { hyp := 555, conc := 1130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 1354, proof := sorry })
                      (RArray.leaf { hyp := 555, conc := 2382, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 2537, proof := sorry })
                      (RArray.leaf { hyp := 555, conc := 2981, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 3090, proof := sorry })
                      (RArray.leaf { hyp := 555, conc := 42, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 555, conc := 774, proof := sorry })
                      (RArray.leaf { hyp := 557, conc := 587, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 54, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 54, conc := 613, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 54, conc := 816, proof := sorry })
                      (RArray.leaf { hyp := 570, conc := 519, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 571, conc := 521, proof := sorry })
                      (RArray.leaf { hyp := 572, conc := 1295, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 574, conc := 499, proof := sorry })
                      (RArray.leaf { hyp := 578, conc := 505, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 56, conc := 60, proof := sorry })
                      (RArray.leaf { hyp := 590, conc := 1528, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 590, conc := 243, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 592, conc := 597, proof := sorry })
                      (RArray.leaf { hyp := 613, conc := 0, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 614, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 615, conc := 46, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 616, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 617, conc := 414, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 620, conc := 624, proof := sorry })
                      (RArray.leaf { hyp := 623, conc := 49, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 624, conc := 48, proof := sorry })
                      (RArray.leaf { hyp := 625, conc := 623, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 626, conc := 2851, proof := sorry })
                      (RArray.leaf { hyp := 626, conc := 8, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 61, conc := 718, proof := sorry })
                      (RArray.leaf { hyp := 630, conc := 653, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 633, conc := 3, proof := sorry })
                      (RArray.leaf { hyp := 634, conc := 851, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 635, conc := 854, proof := sorry })
                      (RArray.leaf { hyp := 636, conc := 649, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 62, conc := 1921, proof := sorry })
                      (RArray.leaf { hyp := 62, conc := 22, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 640, conc := 3, proof := sorry })
                      (RArray.leaf { hyp := 643, conc := 458, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 644, conc := 54, proof := sorry })
                      (RArray.leaf { hyp := 644, conc := 821, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 645, conc := 55, proof := sorry })
                      (RArray.leaf { hyp := 646, conc := 10, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 648, conc := 57, proof := sorry })
                      (RArray.leaf { hyp := 648, conc := 827, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 63, conc := 97, proof := sorry })
                      (RArray.leaf { hyp := 649, conc := 447, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 650, conc := 53, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 653, conc := 437, proof := sorry })
                      (RArray.leaf { hyp := 654, conc := 657, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 657, conc := 10, proof := sorry })
                      (RArray.leaf { hyp := 658, conc := 3, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 660, conc := 847, proof := sorry })
                      (RArray.leaf { hyp := 660, conc := 859, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 665, conc := 1597, proof := sorry })
                      (RArray.leaf { hyp := 667, conc := 495, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 65, conc := 169, proof := sorry })
                      (RArray.leaf { hyp := 65, conc := 280, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 670, conc := 672, proof := sorry })
                      (RArray.leaf { hyp := 671, conc := 800, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 672, conc := 1293, proof := sorry })
                      (RArray.leaf { hyp := 673, conc := 667, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 677, conc := 1695, proof := sorry })
                      (RArray.leaf { hyp := 66, conc := 3143, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 66, conc := 919, proof := sorry })
                      (RArray.leaf { hyp := 680, conc := 704, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 681, conc := 38, proof := sorry })
                      (RArray.leaf { hyp := 681, conc := 868, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 682, conc := 2940, proof := sorry })
                      (RArray.leaf { hyp := 683, conc := 758, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 686, conc := 1296, proof := sorry })
                      (RArray.leaf { hyp := 687, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 688, conc := 1349, proof := sorry })
                      (RArray.leaf { hyp := 689, conc := 4688, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 690, conc := 1975, proof := sorry })
                      (RArray.leaf { hyp := 691, conc := 1357, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 693, conc := 671, proof := sorry })
                      (RArray.leaf { hyp := 694, conc := 1992, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 695, conc := 1, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 697, conc := 1534, proof := sorry })
                      (RArray.leaf { hyp := 702, conc := 1433, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 702, conc := 4306, proof := sorry })
                      (RArray.leaf { hyp := 704, conc := 2900, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 707, conc := 1975, proof := sorry })
                      (RArray.leaf { hyp := 708, conc := 1538, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 709, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 710, conc := 724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 712, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 713, conc := 1119, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 713, conc := 2337, proof := sorry })
                      (RArray.leaf { hyp := 713, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 713, conc := 510, proof := sorry })
                      (RArray.leaf { hyp := 714, conc := 1, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 715, conc := 1527, proof := sorry })
                      (RArray.leaf { hyp := 718, conc := 77, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 70, conc := 5, proof := sorry })
                      (RArray.leaf { hyp := 722, conc := 1477, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 722, conc := 1505, proof := sorry })
                      (RArray.leaf { hyp := 722, conc := 363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 722, conc := 3876, proof := sorry })
                      (RArray.leaf { hyp := 722, conc := 4319, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 722, conc := 64, proof := sorry })
                      (RArray.leaf { hyp := 722, conc := 831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 722, conc := 871, proof := sorry })
                      (RArray.leaf { hyp := 722, conc := 908, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 723, conc := 2364, proof := sorry })
                      (RArray.leaf { hyp := 724, conc := 491, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 726, conc := 963, proof := sorry })
                      (RArray.leaf { hyp := 71, conc := 908, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 730, conc := 1542, proof := sorry })
                      (RArray.leaf { hyp := 730, conc := 4621, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 740, conc := 1521, proof := sorry })
                      (RArray.leaf { hyp := 741, conc := 83, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 742, conc := 84, proof := sorry })
                      (RArray.leaf { hyp := 743, conc := 1602, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 744, conc := 2703, proof := sorry })
                      (RArray.leaf { hyp := 745, conc := 2991, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 745, conc := 4331, proof := sorry })
                      (RArray.leaf { hyp := 747, conc := 781, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 748, conc := 555, proof := sorry })
                      (RArray.leaf { hyp := 73, conc := 1004, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 73, conc := 1005, proof := sorry })
                      (RArray.leaf { hyp := 73, conc := 1006, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 73, conc := 1009, proof := sorry })
                      (RArray.leaf { hyp := 73, conc := 1010, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 73, conc := 1011, proof := sorry })
                      (RArray.leaf { hyp := 749, conc := 750, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 750, conc := 2931, proof := sorry })
                      (RArray.leaf { hyp := 750, conc := 692, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 756, conc := 1509, proof := sorry })
                      (RArray.leaf { hyp := 757, conc := 670, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 758, conc := 1180, proof := sorry })
                      (RArray.leaf { hyp := 760, conc := 693, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 764, conc := 1576, proof := sorry })
                      (RArray.leaf { hyp := 764, conc := 4022, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 764, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 764, conc := 4225, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 764, conc := 4361, proof := sorry })
                      (RArray.leaf { hyp := 764, conc := 730, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 773, conc := 1580, proof := sorry })
                      (RArray.leaf { hyp := 774, conc := 2927, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 775, conc := 791, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 777, conc := 1589, proof := sorry })
                      (RArray.leaf { hyp := 781, conc := 734, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 77, conc := 756, proof := sorry })
                      (RArray.leaf { hyp := 791, conc := 1922, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 800, conc := 81, proof := sorry })
                      (RArray.leaf { hyp := 805, conc := 1464, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 816, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 817, conc := 98, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 819, conc := 7, proof := sorry })
                      (RArray.leaf { hyp := 820, conc := 99, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 821, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 822, conc := 7, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 823, conc := 1030, proof := sorry })
                      (RArray.leaf { hyp := 823, conc := 1224, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 823, conc := 1630, proof := sorry })
                      (RArray.leaf { hyp := 823, conc := 2445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 823, conc := 3457, proof := sorry })
                      (RArray.leaf { hyp := 823, conc := 423, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 826, conc := 101, proof := sorry })
                      (RArray.leaf { hyp := 826, conc := 414, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 827, conc := 48, proof := sorry })
                      (RArray.leaf { hyp := 828, conc := 1031, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 828, conc := 422, proof := sorry })
                      (RArray.leaf { hyp := 829, conc := 102, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 830, conc := 1226, proof := sorry })
                      (RArray.leaf { hyp := 830, conc := 1632, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 830, conc := 2451, proof := sorry })
                      (RArray.leaf { hyp := 830, conc := 3459, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 833, conc := 103, proof := sorry })
                      (RArray.leaf { hyp := 836, conc := 104, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 836, conc := 106, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 838, conc := 1066, proof := sorry })
                      (RArray.leaf { hyp := 838, conc := 1228, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 838, conc := 1248, proof := sorry })
                      (RArray.leaf { hyp := 838, conc := 1259, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 839, conc := 9, proof := sorry })
                      (RArray.leaf { hyp := 840, conc := 1260, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 843, conc := 106, proof := sorry })
                      (RArray.leaf { hyp := 843, conc := 10, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 846, conc := 107, proof := sorry })
                      (RArray.leaf { hyp := 847, conc := 834, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 848, conc := 850, proof := sorry })
                      (RArray.leaf { hyp := 849, conc := 10, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 850, conc := 108, proof := sorry })
                      (RArray.leaf { hyp := 850, conc := 1256, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 851, conc := 51, proof := sorry })
                      (RArray.leaf { hyp := 852, conc := 455, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 853, conc := 1030, proof := sorry })
                      (RArray.leaf { hyp := 853, conc := 1034, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 853, conc := 1227, proof := sorry })
                      (RArray.leaf { hyp := 853, conc := 1230, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 853, conc := 377, proof := sorry })
                      (RArray.leaf { hyp := 853, conc := 429, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 855, conc := 54, proof := sorry })
                      (RArray.leaf { hyp := 856, conc := 3, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 857, conc := 10, proof := sorry })
                      (RArray.leaf { hyp := 861, conc := 3, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 863, conc := 377, proof := sorry })
                      (RArray.leaf { hyp := 863, conc := 660, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 868, conc := 810, proof := sorry })
                      (RArray.leaf { hyp := 870, conc := 1, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 873, conc := 3113, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 875, conc := 2983, proof := sorry })
                      (RArray.leaf { hyp := 876, conc := 14, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 876, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 879, conc := 218, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 879, conc := 4646, proof := sorry })
                      (RArray.leaf { hyp := 880, conc := 1, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 883, conc := 757, proof := sorry })
                      (RArray.leaf { hyp := 884, conc := 937, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 885, conc := 3176, proof := sorry })
                      (RArray.leaf { hyp := 886, conc := 2754, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 888, conc := 1612, proof := sorry })
                      (RArray.leaf { hyp := 889, conc := 744, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 890, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 892, conc := 954, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 893, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 894, conc := 1097, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 894, conc := 1570, proof := sorry })
                      (RArray.leaf { hyp := 894, conc := 2281, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 894, conc := 2401, proof := sorry })
                      (RArray.leaf { hyp := 894, conc := 2778, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 894, conc := 2807, proof := sorry })
                      (RArray.leaf { hyp := 894, conc := 2981, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 894, conc := 3803, proof := sorry })
                      (RArray.leaf { hyp := 894, conc := 860, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 894, conc := 961, proof := sorry })
                      (RArray.leaf { hyp := 896, conc := 976, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 897, conc := 2315, proof := sorry })
                      (RArray.leaf { hyp := 898, conc := 14, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 907, conc := 944, proof := sorry })
                      (RArray.leaf { hyp := 908, conc := 3886, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 908, conc := 54, proof := sorry })
                      (RArray.leaf { hyp := 908, conc := 702, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 908, conc := 71, proof := sorry })
                      (RArray.leaf { hyp := 909, conc := 1628, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 909, conc := 1924, proof := sorry })
                      (RArray.leaf { hyp := 909, conc := 503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 910, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 911, conc := 988, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 912, conc := 3150, proof := sorry })
                      (RArray.leaf { hyp := 913, conc := 1052, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 913, conc := 15, proof := sorry })
                      (RArray.leaf { hyp := 913, conc := 1928, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 913, conc := 454, proof := sorry })
                      (RArray.leaf { hyp := 915, conc := 1425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 915, conc := 358, proof := sorry })
                      (RArray.leaf { hyp := 915, conc := 3861, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 915, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 915, conc := 641, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 917, conc := 1, proof := sorry })
                      (RArray.leaf { hyp := 918, conc := 715, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 921, conc := 954, proof := sorry })
                      (RArray.leaf { hyp := 925, conc := 1563, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 926, conc := 740, proof := sorry })
                      (RArray.leaf { hyp := 927, conc := 1875, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 927, conc := 2473, proof := sorry })
                      (RArray.leaf { hyp := 927, conc := 2481, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 927, conc := 2537, proof := sorry })
                      (RArray.leaf { hyp := 927, conc := 542, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 929, conc := 781, proof := sorry })
                      (RArray.leaf { hyp := 933, conc := 4199, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 933, conc := 777, proof := sorry })
                      (RArray.leaf { hyp := 942, conc := 892, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 943, conc := 1764, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 944, conc := 82, proof := sorry })
                      (RArray.leaf { hyp := 946, conc := 3896, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 946, conc := 722, proof := sorry })
                      (RArray.leaf { hyp := 947, conc := 1, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 948, conc := 961, proof := sorry })
                      (RArray.leaf { hyp := 950, conc := 971, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 951, conc := 1739, proof := sorry })
                      (RArray.leaf { hyp := 951, conc := 913, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 951, conc := 927, proof := sorry })
                      (RArray.leaf { hyp := 952, conc := 1, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 953, conc := 987, proof := sorry })
                      (RArray.leaf { hyp := 956, conc := 990, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 959, conc := 1443, proof := sorry })
                      (RArray.leaf { hyp := 959, conc := 1477, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 959, conc := 1559, proof := sorry })
                      (RArray.leaf { hyp := 959, conc := 363, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 959, conc := 3896, proof := sorry })
                      (RArray.leaf { hyp := 959, conc := 4688, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 960, conc := 3025, proof := sorry })
                      (RArray.leaf { hyp := 961, conc := 545, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 963, conc := 1593, proof := sorry })
                      (RArray.leaf { hyp := 967, conc := 764, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 976, conc := 93, proof := sorry })
                      (RArray.leaf { hyp := 977, conc := 10, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 977, conc := 1745, proof := sorry })
                      (RArray.leaf { hyp := 977, conc := 2465, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 977, conc := 2575, proof := sorry })
                      (RArray.leaf { hyp := 977, conc := 2601, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 977, conc := 3285, proof := sorry })
                      (RArray.leaf { hyp := 977, conc := 3905, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 977, conc := 4619, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 978, conc := 2944, proof := sorry })
                      (RArray.leaf { hyp := 980, conc := 730, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 984, conc := 1013, proof := sorry })
                      (RArray.leaf { hyp := 998, conc := 85, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 98, conc := 0, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 99, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 1223, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 151, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 1629, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 2035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 204, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 2442, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 2645, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 307, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 3659, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 4394, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 822, proof := sorry })
                      (RArray.leaf { hyp := 14, conc := 755, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 29, conc := 2988, proof := sorry })
                      (RArray.leaf { hyp := 312, conc := 3471, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 312, conc := 3677, proof := sorry })
                      (RArray.leaf { hyp := 314, conc := 3658, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3268, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 325, conc := 3521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3288, conc := 3698, proof := sorry })
                      (RArray.leaf { hyp := 3289, conc := 319, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3291, conc := 3287, proof := sorry })
                      (RArray.leaf { hyp := 3311, conc := 3337, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 331, conc := 4481, proof := sorry })
                      (RArray.leaf { hyp := 3329, conc := 3263, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3329, conc := 3311, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3329, conc := 3321, proof := sorry })
                      (RArray.leaf { hyp := 3329, conc := 3325, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3329, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 3329, conc := 4339, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3330, conc := 3533, proof := sorry })
                      (RArray.leaf { hyp := 332, conc := 3721, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3347, conc := 394, proof := sorry })
                      (RArray.leaf { hyp := 3349, conc := 3572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3349, conc := 4589, proof := sorry })
                      (RArray.leaf { hyp := 3354, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3354, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 3354, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3355, conc := 3366, proof := sorry })
                      (RArray.leaf { hyp := 334, conc := 358, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 334, conc := 4434, proof := sorry })
                      (RArray.leaf { hyp := 3361, conc := 3546, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3361, conc := 402, proof := sorry })
                      (RArray.leaf { hyp := 3361, conc := 4526, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3363, conc := 3369, proof := sorry })
                      (RArray.leaf { hyp := 3369, conc := 3552, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3369, conc := 4022, proof := sorry })
                      (RArray.leaf { hyp := 3379, conc := 3396, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3382, conc := 4544, proof := sorry })
                      (RArray.leaf { hyp := 3383, conc := 3430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3387, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 3387, conc := 3413, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 337, conc := 3350, proof := sorry })
                      (RArray.leaf { hyp := 337, conc := 4561, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3395, conc := 3447, proof := sorry })
                      (RArray.leaf { hyp := 3396, conc := 3430, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3397, conc := 3809, proof := sorry })
                      (RArray.leaf { hyp := 3397, conc := 3931, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3399, conc := 3585, proof := sorry })
                      (RArray.leaf { hyp := 3403, conc := 3496, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3407, conc := 3657, proof := sorry })
                      (RArray.leaf { hyp := 3410, conc := 3412, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3410, conc := 3429, proof := sorry })
                      (RArray.leaf { hyp := 3416, conc := 3587, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3416, conc := 4161, proof := sorry })
                      (RArray.leaf { hyp := 3421, conc := 3425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3421, conc := 3440, proof := sorry })
                      (RArray.leaf { hyp := 3470, conc := 311, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 33, conc := 4242, proof := sorry })
                      (RArray.leaf { hyp := 3531, conc := 3534, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3555, conc := 4064, proof := sorry })
                      (RArray.leaf { hyp := 3565, conc := 4242, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3566, conc := 4199, proof := sorry })
                      (RArray.leaf { hyp := 3566, conc := 4530, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3585, conc := 3588, proof := sorry })
                      (RArray.leaf { hyp := 3585, conc := 3840, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3602, conc := 3860, proof := sorry })
                      (RArray.leaf { hyp := 3616, conc := 4225, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3619, conc := 3587, proof := sorry })
                      (RArray.leaf { hyp := 361, conc := 3658, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 364, conc := 3684, proof := sorry })
                      (RArray.leaf { hyp := 364, conc := 3877, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3714, conc := 325, proof := sorry })
                      (RArray.leaf { hyp := 3714, conc := 374, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3755, conc := 3687, proof := sorry })
                      (RArray.leaf { hyp := 374, conc := 3914, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3769, conc := 3525, proof := sorry })
                      (RArray.leaf { hyp := 3769, conc := 4145, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 376, conc := 3721, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3809, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 3809, conc := 4022, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3822, conc := 3687, proof := sorry })
                      (RArray.leaf { hyp := 3840, conc := 3860, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 383, conc := 306, proof := sorry })
                      (RArray.leaf { hyp := 383, conc := 4434, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3862, conc := 359, proof := sorry })
                      (RArray.leaf { hyp := 389, conc := 4246, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3923, conc := 3252, proof := sorry })
                      (RArray.leaf { hyp := 3929, conc := 3323, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3931, conc := 3322, proof := sorry })
                      (RArray.leaf { hyp := 3952, conc := 4266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3955, conc := 4266, proof := sorry })
                      (RArray.leaf { hyp := 3957, conc := 4000, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3958, conc := 3993, proof := sorry })
                      (RArray.leaf { hyp := 3962, conc := 4266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 397, conc := 4219, proof := sorry })
                      (RArray.leaf { hyp := 3997, conc := 4001, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4025, conc := 3333, proof := sorry })
                      (RArray.leaf { hyp := 4076, conc := 4068, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4080, conc := 3658, proof := sorry })
                      (RArray.leaf { hyp := 4084, conc := 368, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4086, conc := 3690, proof := sorry })
                      (RArray.leaf { hyp := 39, conc := 3661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 39, conc := 3683, proof := sorry })
                      (RArray.leaf { hyp := 39, conc := 3691, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4116, conc := 4122, proof := sorry })
                      (RArray.leaf { hyp := 4121, conc := 4131, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4123, conc := 4149, proof := sorry })
                      (RArray.leaf { hyp := 4128, conc := 4135, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4131, conc := 4068, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4131, conc := 4132, proof := sorry })
                      (RArray.leaf { hyp := 4131, conc := 4133, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4131, conc := 4134, proof := sorry })
                      (RArray.leaf { hyp := 4131, conc := 4653, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4141, conc := 4123, proof := sorry })
                      (RArray.leaf { hyp := 4142, conc := 4134, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4142, conc := 4145, proof := sorry })
                      (RArray.leaf { hyp := 4146, conc := 4150, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4146, conc := 4151, proof := sorry })
                      (RArray.leaf { hyp := 4153, conc := 3455, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4153, conc := 3861, proof := sorry })
                      (RArray.leaf { hyp := 4153, conc := 4434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4155, conc := 3955, proof := sorry })
                      (RArray.leaf { hyp := 4158, conc := 4406, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4159, conc := 3328, proof := sorry })
                      (RArray.leaf { hyp := 4159, conc := 3991, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4161, conc := 3307, proof := sorry })
                      (RArray.leaf { hyp := 4161, conc := 3354, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4161, conc := 3416, proof := sorry })
                      (RArray.leaf { hyp := 4161, conc := 3993, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4165, conc := 4235, proof := sorry })
                      (RArray.leaf { hyp := 4169, conc := 329, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4169, conc := 4008, proof := sorry })
                      (RArray.leaf { hyp := 4175, conc := 3902, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4176, conc := 4063, proof := sorry })
                      (RArray.leaf { hyp := 4177, conc := 326, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4196, conc := 3790, proof := sorry })
                      (RArray.leaf { hyp := 4199, conc := 3996, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4201, conc := 3784, proof := sorry })
                      (RArray.leaf { hyp := 4204, conc := 3857, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 3616, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4209, conc := 3769, proof := sorry })
                      (RArray.leaf { hyp := 4215, conc := 4181, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4227, conc := 4240, proof := sorry })
                      (RArray.leaf { hyp := 4228, conc := 3978, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4228, conc := 4269, proof := sorry })
                      (RArray.leaf { hyp := 4243, conc := 3839, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4300, conc := 4276, proof := sorry })
                      (RArray.leaf { hyp := 4330, conc := 4354, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 42, conc := 4357, proof := sorry })
                      (RArray.leaf { hyp := 42, conc := 4543, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4615, conc := 4622, proof := sorry })
                      (RArray.leaf { hyp := 4645, conc := 4669, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 313, conc := 3290, proof := sorry })
                      (RArray.leaf { hyp := 313, conc := 4348, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 315, conc := 4279, proof := sorry })
                      (RArray.leaf { hyp := 316, conc := 4311, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 318, conc := 4336, proof := sorry })
                      (RArray.leaf { hyp := 319, conc := 3302, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3262, conc := 309, proof := sorry })
                      (RArray.leaf { hyp := 3272, conc := 4275, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3287, conc := 4350, proof := sorry })
                      (RArray.leaf { hyp := 3292, conc := 311, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3356, conc := 3399, proof := sorry })
                      (RArray.leaf { hyp := 3358, conc := 3408, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3359, conc := 3405, proof := sorry })
                      (RArray.leaf { hyp := 3366, conc := 3329, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3366, conc := 3383, proof := sorry })
                      (RArray.leaf { hyp := 3366, conc := 3417, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3367, conc := 3437, proof := sorry })
                      (RArray.leaf { hyp := 335, conc := 3558, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3370, conc := 3445, proof := sorry })
                      (RArray.leaf { hyp := 3371, conc := 3447, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3378, conc := 4249, proof := sorry })
                      (RArray.leaf { hyp := 3381, conc := 3448, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3389, conc := 3443, proof := sorry })
                      (RArray.leaf { hyp := 3390, conc := 3452, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3392, conc := 3451, proof := sorry })
                      (RArray.leaf { hyp := 3393, conc := 3453, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3405, conc := 3395, proof := sorry })
                      (RArray.leaf { hyp := 339, conc := 3453, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3417, conc := 3435, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 339, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3422, conc := 351, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 356, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3422, conc := 3575, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 3583, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3422, conc := 3584, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3422, conc := 3980, proof := sorry })
                      (RArray.leaf { hyp := 3422, conc := 3981, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3424, conc := 3428, proof := sorry })
                      (RArray.leaf { hyp := 3431, conc := 3451, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3439, conc := 3443, proof := sorry })
                      (RArray.leaf { hyp := 3444, conc := 3448, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3484, conc := 3471, proof := sorry })
                      (RArray.leaf { hyp := 348, conc := 3614, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 350, conc := 3856, proof := sorry })
                      (RArray.leaf { hyp := 3558, conc := 338, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3559, conc := 3605, proof := sorry })
                      (RArray.leaf { hyp := 3561, conc := 3611, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3562, conc := 3598, proof := sorry })
                      (RArray.leaf { hyp := 3569, conc := 3638, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3570, conc := 3640, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3574, conc := 3650, proof := sorry })
                      (RArray.leaf { hyp := 3584, conc := 3651, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3592, conc := 3646, proof := sorry })
                      (RArray.leaf { hyp := 3593, conc := 3655, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3595, conc := 3654, proof := sorry })
                      (RArray.leaf { hyp := 3596, conc := 3656, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3604, conc := 3602, proof := sorry })
                      (RArray.leaf { hyp := 3618, conc := 3631, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3627, conc := 3631, proof := sorry })
                      (RArray.leaf { hyp := 3632, conc := 3656, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3634, conc := 3654, proof := sorry })
                      (RArray.leaf { hyp := 3642, conc := 3646, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 365, conc := 4088, proof := sorry })
                      (RArray.leaf { hyp := 365, conc := 4623, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 367, conc := 359, proof := sorry })
                      (RArray.leaf { hyp := 367, conc := 4591, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3710, conc := 3730, proof := sorry })
                      (RArray.leaf { hyp := 3710, conc := 375, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 370, conc := 4625, proof := sorry })
                      (RArray.leaf { hyp := 3730, conc := 3949, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3738, conc := 3944, proof := sorry })
                      (RArray.leaf { hyp := 373, conc := 3719, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 373, conc := 379, proof := sorry })
                      (RArray.leaf { hyp := 3761, conc := 335, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3761, conc := 3810, proof := sorry })
                      (RArray.leaf { hyp := 3762, conc := 3559, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3765, conc := 3859, proof := sorry })
                      (RArray.leaf { hyp := 3773, conc := 3844, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3776, conc := 3856, proof := sorry })
                      (RArray.leaf { hyp := 3777, conc := 3859, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3784, conc := 4245, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3786, conc := 4245, proof := sorry })
                      (RArray.leaf { hyp := 3792, conc := 4245, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3794, conc := 4245, proof := sorry })
                      (RArray.leaf { hyp := 3807, conc := 3844, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 362, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3733, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 3741, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3742, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 3743, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3744, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 3746, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 381, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 382, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3932, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 3936, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 3940, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 379, conc := 3948, proof := sorry })
                      (RArray.leaf { hyp := 379, conc := 4521, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 317, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3450, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3561, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3569, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3594, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3643, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3653, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3743, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3780, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3797, proof := sorry })
                      (RArray.leaf { hyp := 3810, conc := 3831, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 3846, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 3810, conc := 4578, proof := sorry })
                      (RArray.leaf { hyp := 3811, conc := 3859, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3818, conc := 3834, proof := sorry })
                      (RArray.leaf { hyp := 3820, conc := 3834, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3824, conc := 3840, proof := sorry })
                      (RArray.leaf { hyp := 3826, conc := 3834, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 381, conc := 3949, proof := sorry })
                      (RArray.leaf { hyp := 3890, conc := 3877, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3913, conc := 373, proof := sorry })
                      (RArray.leaf { hyp := 393, conc := 4260, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 395, conc := 4255, proof := sorry })
                      (RArray.leaf { hyp := 3969, conc := 4037, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3977, conc := 4052, proof := sorry })
                      (RArray.leaf { hyp := 396, conc := 4206, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3981, conc := 4057, proof := sorry })
                      (RArray.leaf { hyp := 3984, conc := 4061, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3985, conc := 4062, proof := sorry })
                      (RArray.leaf { hyp := 3987, conc := 3990, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3995, conc := 3998, proof := sorry })
                      (RArray.leaf { hyp := 38, conc := 3967, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 38, conc := 3975, proof := sorry })
                      (RArray.leaf { hyp := 38, conc := 398, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 38, conc := 402, proof := sorry })
                      (RArray.leaf { hyp := 399, conc := 4266, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4015, conc := 4052, proof := sorry })
                      (RArray.leaf { hyp := 4018, conc := 4060, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4019, conc := 4062, proof := sorry })
                      (RArray.leaf { hyp := 4021, conc := 4024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4028, conc := 4037, proof := sorry })
                      (RArray.leaf { hyp := 401, conc := 4240, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4029, conc := 4032, proof := sorry })
                      (RArray.leaf { hyp := 4045, conc := 4060, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4046, conc := 4061, proof := sorry })
                      (RArray.leaf { hyp := 4068, conc := 4596, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4093, conc := 4067, proof := sorry })
                      (RArray.leaf { hyp := 4096, conc := 359, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4101, conc := 4590, proof := sorry })
                      (RArray.leaf { hyp := 4107, conc := 366, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4116, conc := 4136, proof := sorry })
                      (RArray.leaf { hyp := 4122, conc := 4125, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4124, conc := 4125, proof := sorry })
                      (RArray.leaf { hyp := 4136, conc := 4138, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4138, conc := 4139, proof := sorry })
                      (RArray.leaf { hyp := 4144, conc := 4147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4146, conc := 4147, proof := sorry })
                      (RArray.leaf { hyp := 4168, conc := 4266, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4172, conc := 4240, proof := sorry })
                      (RArray.leaf { hyp := 4180, conc := 4255, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4184, conc := 4260, proof := sorry })
                      (RArray.leaf { hyp := 4187, conc := 4264, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4188, conc := 4265, proof := sorry })
                      (RArray.leaf { hyp := 4190, conc := 4155, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4192, conc := 4190, proof := sorry })
                      (RArray.leaf { hyp := 4198, conc := 4201, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 333, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 336, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3380, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3381, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3389, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3394, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3397, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3402, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3403, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3433, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3454, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 345, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3601, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3619, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3622, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 3795, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 4016, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 4051, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 4161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 4175, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 4214, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 40, conc := 4250, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 43, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4200, conc := 4198, proof := sorry })
                      (RArray.leaf { hyp := 4218, conc := 4255, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4221, conc := 4263, proof := sorry })
                      (RArray.leaf { hyp := 4224, conc := 4165, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4226, conc := 4224, proof := sorry })
                      (RArray.leaf { hyp := 4232, conc := 4235, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4248, conc := 4263, proof := sorry })
                      (RArray.leaf { hyp := 4249, conc := 4264, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4267, conc := 4281, proof := sorry })
                      (RArray.leaf { hyp := 4268, conc := 4315, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4269, conc := 4340, proof := sorry })
                      (RArray.leaf { hyp := 4270, conc := 4360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4271, conc := 4350, proof := sorry })
                      (RArray.leaf { hyp := 4272, conc := 4331, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4273, conc := 4374, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4274, conc := 4306, proof := sorry })
                      (RArray.leaf { hyp := 4276, conc := 4293, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4277, conc := 4309, proof := sorry })
                      (RArray.leaf { hyp := 4277, conc := 4322, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4277, conc := 4333, proof := sorry })
                      (RArray.leaf { hyp := 4277, conc := 4361, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4278, conc := 4323, proof := sorry })
                      (RArray.leaf { hyp := 4279, conc := 4345, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4280, conc := 4308, proof := sorry })
                      (RArray.leaf { hyp := 4280, conc := 4325, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4280, conc := 4336, proof := sorry })
                      (RArray.leaf { hyp := 4284, conc := 4341, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4286, conc := 4339, proof := sorry })
                      (RArray.leaf { hyp := 4288, conc := 4316, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4288, conc := 4317, proof := sorry })
                      (RArray.leaf { hyp := 4291, conc := 4297, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4294, conc := 4370, proof := sorry })
                      (RArray.leaf { hyp := 4299, conc := 4373, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4301, conc := 4374, proof := sorry })
                      (RArray.leaf { hyp := 4302, conc := 4375, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4305, conc := 4378, proof := sorry })
                      (RArray.leaf { hyp := 4309, conc := 4353, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4314, conc := 4356, proof := sorry })
                      (RArray.leaf { hyp := 4316, conc := 4360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4318, conc := 4360, proof := sorry })
                      (RArray.leaf { hyp := 4321, conc := 4362, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4322, conc := 4377, proof := sorry })
                      (RArray.leaf { hyp := 4327, conc := 4292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4327, conc := 4302, proof := sorry })
                      (RArray.leaf { hyp := 4328, conc := 4378, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4329, conc := 4299, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4332, conc := 4374, proof := sorry })
                      (RArray.leaf { hyp := 4334, conc := 4378, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4338, conc := 4314, proof := sorry })
                      (RArray.leaf { hyp := 4339, conc := 4359, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4341, conc := 4360, proof := sorry })
                      (RArray.leaf { hyp := 4344, conc := 4292, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4344, conc := 4294, proof := sorry })
                      (RArray.leaf { hyp := 4347, conc := 4377, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4349, conc := 4374, proof := sorry })
                      (RArray.leaf { hyp := 4388, conc := 4590, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4389, conc := 4622, proof := sorry })
                      (RArray.leaf { hyp := 4391, conc := 4650, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4392, conc := 4669, proof := sorry })
                      (RArray.leaf { hyp := 4413, conc := 4421, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4421, conc := 4430, proof := sorry })
                      (RArray.leaf { hyp := 4450, conc := 4458, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4458, conc := 4467, proof := sorry })
                      (RArray.leaf { hyp := 4461, conc := 4335, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4487, conc := 4504, proof := sorry })
                      (RArray.leaf { hyp := 4495, conc := 4477, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4495, conc := 4487, proof := sorry })
                      (RArray.leaf { hyp := 4495, conc := 4491, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4495, conc := 4501, proof := sorry })
                      (RArray.leaf { hyp := 4495, conc := 4503, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4498, conc := 4354, proof := sorry })
                      (RArray.leaf { hyp := 4527, conc := 4505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4529, conc := 4575, proof := sorry })
                      (RArray.leaf { hyp := 4537, conc := 4580, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4550, conc := 4529, proof := sorry })
                      (RArray.leaf { hyp := 4554, conc := 4537, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4564, conc := 4579, proof := sorry })
                      (RArray.leaf { hyp := 4569, conc := 4428, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4569, conc := 4465, proof := sorry })
                      (RArray.leaf { hyp := 4569, conc := 4535, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4569, conc := 4553, proof := sorry })
                      (RArray.leaf { hyp := 4569, conc := 4574, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4582, conc := 4596, proof := sorry })
                      (RArray.leaf { hyp := 4583, conc := 4630, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4584, conc := 4655, proof := sorry })
                      (RArray.leaf { hyp := 4585, conc := 4675, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4586, conc := 4665, proof := sorry })
                      (RArray.leaf { hyp := 4587, conc := 4646, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4588, conc := 4689, proof := sorry })
                      (RArray.leaf { hyp := 4589, conc := 4621, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4591, conc := 4608, proof := sorry })
                      (RArray.leaf { hyp := 4592, conc := 4692, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4593, conc := 4638, proof := sorry })
                      (RArray.leaf { hyp := 4594, conc := 4660, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4595, conc := 4640, proof := sorry })
                      (RArray.leaf { hyp := 4595, conc := 4643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4599, conc := 4656, proof := sorry })
                      (RArray.leaf { hyp := 4600, conc := 4596, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4601, conc := 4674, proof := sorry })
                      (RArray.leaf { hyp := 4602, conc := 4596, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4603, conc := 4631, proof := sorry })
                      (RArray.leaf { hyp := 4606, conc := 4666, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4609, conc := 4657, proof := sorry })
                      (RArray.leaf { hyp := 4609, conc := 4659, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4614, conc := 4688, proof := sorry })
                      (RArray.leaf { hyp := 4617, conc := 4642, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4624, conc := 4662, proof := sorry })
                      (RArray.leaf { hyp := 4629, conc := 4671, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4631, conc := 4675, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4633, conc := 4675, proof := sorry })
                      (RArray.leaf { hyp := 4636, conc := 4657, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4636, conc := 4658, proof := sorry })
                      (RArray.leaf { hyp := 4637, conc := 4692, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4644, conc := 4614, proof := sorry })
                      (RArray.leaf { hyp := 4647, conc := 4689, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4648, conc := 4692, proof := sorry })
                      (RArray.leaf { hyp := 4649, conc := 4693, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4653, conc := 4629, proof := sorry })
                      (RArray.leaf { hyp := 4654, conc := 4601, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4656, conc := 4675, proof := sorry })
                      (RArray.leaf { hyp := 4658, conc := 4677, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4659, conc := 4685, proof := sorry })
                      (RArray.leaf { hyp := 4662, conc := 4692, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4664, conc := 4667, proof := sorry })
                      (RArray.leaf { hyp := 4667, conc := 4693, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4668, conc := 4692, proof := sorry })
                      (RArray.leaf { hyp := 37, conc := 4601, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 38, conc := 4339, proof := sorry })
                      (RArray.leaf { hyp := 4284, conc := 4270, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4297, conc := 4312, proof := sorry })
                      (RArray.leaf { hyp := 4308, conc := 4305, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4322, conc := 4277, proof := sorry })
                      (RArray.leaf { hyp := 4325, conc := 4337, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4327, conc := 4329, proof := sorry })
                      (RArray.leaf { hyp := 4344, conc := 4339, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4346, conc := 4355, proof := sorry })
                      (RArray.leaf { hyp := 4347, conc := 4277, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4352, conc := 4348, proof := sorry })
                      (RArray.leaf { hyp := 4394, conc := 4281, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4408, conc := 4306, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4431, conc := 4315, proof := sorry })
                      (RArray.leaf { hyp := 4445, conc := 4331, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4468, conc := 4340, proof := sorry })
                      (RArray.leaf { hyp := 4482, conc := 4350, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4505, conc := 4360, proof := sorry })
                      (RArray.leaf { hyp := 4506, conc := 4356, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4507, conc := 4359, proof := sorry })
                      (RArray.leaf { hyp := 4509, conc := 4356, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4510, conc := 4356, proof := sorry })
                      (RArray.leaf { hyp := 4515, conc := 4359, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4526, conc := 4356, proof := sorry })
                      (RArray.leaf { hyp := 4528, conc := 4373, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4532, conc := 4373, proof := sorry })
                      (RArray.leaf { hyp := 4541, conc := 4359, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4545, conc := 4373, proof := sorry })
                      (RArray.leaf { hyp := 4549, conc := 4377, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4599, conc := 4585, proof := sorry })
                      (RArray.leaf { hyp := 4606, conc := 4588, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4609, conc := 4601, proof := sorry })
                      (RArray.leaf { hyp := 4612, conc := 4627, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4620, conc := 4612, proof := sorry })
                      (RArray.leaf { hyp := 4623, conc := 4620, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4636, conc := 4629, proof := sorry })
                      (RArray.leaf { hyp := 4637, conc := 4592, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4640, conc := 4652, proof := sorry })
                      (RArray.leaf { hyp := 4643, conc := 4640, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4661, conc := 4670, proof := sorry })
                      (RArray.leaf { hyp := 4663, conc := 4661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4667, conc := 4663, proof := sorry })
                      (RArray.leaf { hyp := 9, conc := 1852, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 9, conc := 3321, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 9, conc := 3934, proof := sorry })
                      (RArray.leaf { hyp := 9, conc := 4315, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 9, conc := 431, proof := sorry })
                      (RArray.leaf { hyp := 10, conc := 1063, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 10, conc := 1864, proof := sorry })
                      (RArray.leaf { hyp := 10, conc := 3322, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 10, conc := 3942, proof := sorry })
                      (RArray.leaf { hyp := 10, conc := 443, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 10, conc := 849, proof := sorry })
                      (RArray.leaf { hyp := 12, conc := 1145, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 12, conc := 482, proof := sorry })
                      (RArray.leaf { hyp := 13, conc := 1154, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 13, conc := 1976, proof := sorry })
                      (RArray.leaf { hyp := 13, conc := 3330, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 13, conc := 4331, proof := sorry })
                      (RArray.leaf { hyp := 13, conc := 488, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 15, conc := 1948, proof := sorry })
                      (RArray.leaf { hyp := 15, conc := 3333, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 15, conc := 4022, proof := sorry })
                      (RArray.leaf { hyp := 15, conc := 574, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 22, conc := 1628, proof := sorry })
                      (RArray.leaf { hyp := 22, conc := 2440, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 22, conc := 3049, proof := sorry })
                      (RArray.leaf { hyp := 22, conc := 3521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 22, conc := 4117, proof := sorry })
                      (RArray.leaf { hyp := 23, conc := 3056, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 23, conc := 4123, proof := sorry })
                      (RArray.leaf { hyp := 24, conc := 1649, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 24, conc := 3070, proof := sorry })
                      (RArray.leaf { hyp := 24, conc := 3524, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 24, conc := 4137, proof := sorry })
                      (RArray.leaf { hyp := 24, conc := 4630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 25, conc := 2484, proof := sorry })
                      (RArray.leaf { hyp := 25, conc := 3093, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 25, conc := 3525, proof := sorry })
                      (RArray.leaf { hyp := 25, conc := 4145, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 26, conc := 4675, proof := sorry })
                      (RArray.leaf { hyp := 27, conc := 1700, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 27, conc := 2566, proof := sorry })
                      (RArray.leaf { hyp := 27, conc := 3532, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 27, conc := 4191, proof := sorry })
                      (RArray.leaf { hyp := 28, conc := 2575, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 28, conc := 2978, proof := sorry })
                      (RArray.leaf { hyp := 28, conc := 3194, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 28, conc := 4199, proof := sorry })
                      (RArray.leaf { hyp := 306, conc := 3252, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 307, conc := 4281, proof := sorry })
                      (RArray.leaf { hyp := 308, conc := 3254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 308, conc := 4315, proof := sorry })
                      (RArray.leaf { hyp := 309, conc := 3265, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 309, conc := 4340, proof := sorry })
                      (RArray.leaf { hyp := 310, conc := 4360, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 311, conc := 3287, proof := sorry })
                      (RArray.leaf { hyp := 312, conc := 3258, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 312, conc := 4331, proof := sorry })
                      (RArray.leaf { hyp := 313, conc := 3479, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 313, conc := 4374, proof := sorry })
                      (RArray.leaf { hyp := 314, conc := 3260, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 314, conc := 4306, proof := sorry })
                      (RArray.leaf { hyp := 315, conc := 3297, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 316, conc := 3298, proof := sorry })
                      (RArray.leaf { hyp := 317, conc := 3299, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 317, conc := 4377, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 318, conc := 3301, proof := sorry })
                      (RArray.leaf { hyp := 30, conc := 1745, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 30, conc := 2604, proof := sorry })
                      (RArray.leaf { hyp := 30, conc := 2760, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 30, conc := 3166, proof := sorry })
                      (RArray.leaf { hyp := 30, conc := 3536, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 30, conc := 4225, proof := sorry })
                      (RArray.leaf { hyp := 322, conc := 3305, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 324, conc := 3315, proof := sorry })
                      (RArray.leaf { hyp := 324, conc := 3517, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 325, conc := 3318, proof := sorry })
                      (RArray.leaf { hyp := 328, conc := 3337, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 329, conc := 3339, proof := sorry })
                      (RArray.leaf { hyp := 331, conc := 3714, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 332, conc := 3352, proof := sorry })
                      (RArray.leaf { hyp := 333, conc := 4356, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 334, conc := 3342, proof := sorry })
                      (RArray.leaf { hyp := 3378, conc := 3447, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 336, conc := 3372, proof := sorry })
                      (RArray.leaf { hyp := 3380, conc := 3422, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3380, conc := 3446, proof := sorry })
                      (RArray.leaf { hyp := 3386, conc := 3442, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3388, conc := 3441, proof := sorry })
                      (RArray.leaf { hyp := 339, conc := 3376, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3412, conc := 3427, proof := sorry })
                      (RArray.leaf { hyp := 3414, conc := 3418, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3420, conc := 3422, proof := sorry })
                      (RArray.leaf { hyp := 341, conc := 3453, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 342, conc := 3430, proof := sorry })
                      (RArray.leaf { hyp := 343, conc := 347, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 343, conc := 355, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 345, conc := 3601, proof := sorry })
                      (RArray.leaf { hyp := 347, conc := 3612, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 349, conc := 3448, proof := sorry })
                      (RArray.leaf { hyp := 349, conc := 350, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 351, conc := 3447, proof := sorry })
                      (RArray.leaf { hyp := 3581, conc := 3650, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3583, conc := 3649, proof := sorry })
                      (RArray.leaf { hyp := 3589, conc := 3645, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3591, conc := 3644, proof := sorry })
                      (RArray.leaf { hyp := 358, conc := 4064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 359, conc := 4068, proof := sorry })
                      (RArray.leaf { hyp := 3615, conc := 3630, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3617, conc := 3629, proof := sorry })
                      (RArray.leaf { hyp := 360, conc := 4069, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 360, conc := 4630, proof := sorry })
                      (RArray.leaf { hyp := 3623, conc := 3626, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 361, conc := 4072, proof := sorry })
                      (RArray.leaf { hyp := 361, conc := 4655, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 362, conc := 4078, proof := sorry })
                      (RArray.leaf { hyp := 362, conc := 4675, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 363, conc := 4665, proof := sorry })
                      (RArray.leaf { hyp := 364, conc := 4082, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 364, conc := 4646, proof := sorry })
                      (RArray.leaf { hyp := 365, conc := 3899, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 366, conc := 4095, proof := sorry })
                      (RArray.leaf { hyp := 366, conc := 4621, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 367, conc := 4094, proof := sorry })
                      (RArray.leaf { hyp := 369, conc := 4692, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 370, conc := 4106, proof := sorry })
                      (RArray.leaf { hyp := 371, conc := 4110, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 373, conc := 4116, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 374, conc := 4117, proof := sorry })
                      (RArray.leaf { hyp := 375, conc := 4125, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 376, conc := 4126, proof := sorry })
                      (RArray.leaf { hyp := 377, conc := 4130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 378, conc := 4135, proof := sorry })
                      (RArray.leaf { hyp := 380, conc := 4149, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 383, conc := 4129, proof := sorry })
                      (RArray.leaf { hyp := 384, conc := 3961, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 384, conc := 4127, proof := sorry })
                      (RArray.leaf { hyp := 385, conc := 4007, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 386, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 386, conc := 4166, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 388, conc := 404, proof := sorry })
                      (RArray.leaf { hyp := 391, conc := 408, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 393, conc := 4256, proof := sorry })
                      (RArray.leaf { hyp := 3965, conc := 4032, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3968, conc := 4036, proof := sorry })
                      (RArray.leaf { hyp := 395, conc := 4040, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3976, conc := 4051, proof := sorry })
                      (RArray.leaf { hyp := 3980, conc := 4056, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 1222, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 1425, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 150, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 2034, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 2237, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 254, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 2643, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 2846, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 325, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 3714, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 374, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 46, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 613, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2, conc := 816, proof := sorry })
                      (RArray.leaf { hyp := 2, conc := 98, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 399, conc := 407, proof := sorry })
                      (RArray.leaf { hyp := 4010, conc := 4055, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4014, conc := 4050, proof := sorry })
                      (RArray.leaf { hyp := 4027, conc := 4035, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 401, conc := 3833, proof := sorry })
                      (RArray.leaf { hyp := 403, conc := 4235, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 405, conc := 3860, proof := sorry })
                      (RArray.leaf { hyp := 39, conc := 4340, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 39, conc := 4621, proof := sorry })
                      (RArray.leaf { hyp := 4168, conc := 4235, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4171, conc := 4239, proof := sorry })
                      (RArray.leaf { hyp := 4179, conc := 4254, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4183, conc := 4259, proof := sorry })
                      (RArray.leaf { hyp := 40, conc := 3828, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4213, conc := 4258, proof := sorry })
                      (RArray.leaf { hyp := 4217, conc := 4253, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4230, conc := 4238, proof := sorry })
                      (RArray.leaf { hyp := 4285, conc := 4267, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4287, conc := 4267, proof := sorry })
                      (RArray.leaf { hyp := 4293, conc := 4307, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4295, conc := 4274, proof := sorry })
                      (RArray.leaf { hyp := 4296, conc := 4274, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4303, conc := 4274, proof := sorry })
                      (RArray.leaf { hyp := 4304, conc := 4274, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4310, conc := 4276, proof := sorry })
                      (RArray.leaf { hyp := 4311, conc := 4276, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4317, conc := 4268, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4318, conc := 4285, proof := sorry })
                      (RArray.leaf { hyp := 4323, conc := 4335, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4324, conc := 4272, proof := sorry })
                      (RArray.leaf { hyp := 4326, conc := 4268, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4329, conc := 4290, proof := sorry })
                      (RArray.leaf { hyp := 4330, conc := 4272, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4333, conc := 4295, proof := sorry })
                      (RArray.leaf { hyp := 4336, conc := 4278, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4337, conc := 4310, proof := sorry })
                      (RArray.leaf { hyp := 4338, conc := 4313, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4339, conc := 4283, proof := sorry })
                      (RArray.leaf { hyp := 4341, conc := 4287, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4345, conc := 4354, proof := sorry })
                      (RArray.leaf { hyp := 4353, conc := 4303, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4363, conc := 4289, proof := sorry })
                      (RArray.leaf { hyp := 4364, conc := 4312, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4364, conc := 4337, proof := sorry })
                      (RArray.leaf { hyp := 4364, conc := 4360, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4364, conc := 4362, proof := sorry })
                      (RArray.leaf { hyp := 4364, conc := 4376, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4365, conc := 4364, proof := sorry })
                      (RArray.leaf { hyp := 4371, conc := 4367, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4376, conc := 4371, proof := sorry })
                      (RArray.leaf { hyp := 4380, conc := 4596, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4381, conc := 4630, proof := sorry })
                      (RArray.leaf { hyp := 4382, conc := 4655, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4383, conc := 4675, proof := sorry })
                      (RArray.leaf { hyp := 4384, conc := 4665, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4385, conc := 4646, proof := sorry })
                      (RArray.leaf { hyp := 4386, conc := 4689, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4387, conc := 4621, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4390, conc := 4692, proof := sorry })
                      (RArray.leaf { hyp := 4399, conc := 4671, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4401, conc := 4674, proof := sorry })
                      (RArray.leaf { hyp := 4406, conc := 4671, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4409, conc := 4425, proof := sorry })
                      (RArray.leaf { hyp := 4415, conc := 4688, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4436, conc := 4671, proof := sorry })
                      (RArray.leaf { hyp := 4438, conc := 4674, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4446, conc := 4462, proof := sorry })
                      (RArray.leaf { hyp := 4455, conc := 4688, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4473, conc := 4671, proof := sorry })
                      (RArray.leaf { hyp := 4475, conc := 4674, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4483, conc := 4499, proof := sorry })
                      (RArray.leaf { hyp := 4486, conc := 4503, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4489, conc := 4688, proof := sorry })
                      (RArray.leaf { hyp := 4494, conc := 4502, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 43, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 4533, conc := 4555, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4533, conc := 4560, proof := sorry })
                      (RArray.leaf { hyp := 4533, conc := 4577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4546, conc := 4570, proof := sorry })
                      (RArray.leaf { hyp := 4608, conc := 4622, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4610, conc := 4589, proof := sorry })
                      (RArray.leaf { hyp := 4611, conc := 4589, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4618, conc := 4589, proof := sorry })
                      (RArray.leaf { hyp := 4619, conc := 4589, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4626, conc := 4591, proof := sorry })
                      (RArray.leaf { hyp := 4632, conc := 4583, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4633, conc := 4600, proof := sorry })
                      (RArray.leaf { hyp := 4638, conc := 4650, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 4639, conc := 4587, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 4641, conc := 4583, proof := sorry })
                      (RArray.leaf { hyp := 4644, conc := 4605, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4645, conc := 4587, proof := sorry })
                      (RArray.leaf { hyp := 4647, conc := 4615, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4648, conc := 4610, proof := sorry })
                      (RArray.leaf { hyp := 4651, conc := 4593, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4653, conc := 4628, proof := sorry })
                      (RArray.leaf { hyp := 4654, conc := 4598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4656, conc := 4602, proof := sorry })
                      (RArray.leaf { hyp := 4660, conc := 4669, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4668, conc := 4618, proof := sorry })
                      (RArray.leaf { hyp := 4668, conc := 4641, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4678, conc := 4604, proof := sorry })
                      (RArray.leaf { hyp := 4679, conc := 4693, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4680, conc := 4652, proof := sorry })
                      (RArray.leaf { hyp := 4680, conc := 4677, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 4680, conc := 4690, proof := sorry })
                      (RArray.leaf { hyp := 4680, conc := 4691, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 4686, conc := 4682, proof := sorry })
                      (RArray.leaf { hyp := 4691, conc := 4686, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3, conc := 382, proof := sorry })
                      (RArray.leaf { hyp := 4, conc := 93, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 7, conc := 1019, proof := sorry })
                      (RArray.leaf { hyp := 7, conc := 1831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 7, conc := 3318, proof := sorry })
                      (RArray.leaf { hyp := 7, conc := 3914, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 7, conc := 410, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 1023, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 1838, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 3319, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 8, conc := 3920, proof := sorry })
                      (RArray.leaf { hyp := 8, conc := 4281, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 999, conc := 992, proof := sorry })
                      (RArray.leaf { hyp := 1000, conc := 999, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1001, conc := 1000, proof := sorry })
                      (RArray.leaf { hyp := 1004, conc := 1002, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1009, conc := 1007, proof := sorry })
                      (RArray.leaf { hyp := 1010, conc := 1009, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1011, conc := 1010, proof := sorry })
                      (RArray.leaf { hyp := 1015, conc := 1014, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1016, conc := 1015, proof := sorry })
                      (RArray.leaf { hyp := 1122, conc := 1018, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1171, conc := 1169, proof := sorry })
                      (RArray.leaf { hyp := 1172, conc := 1171, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1176, conc := 1175, proof := sorry })
                      (RArray.leaf { hyp := 1177, conc := 1176, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1184, conc := 1178, proof := sorry })
                      (RArray.leaf { hyp := 1185, conc := 1184, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1188, conc := 1186, proof := sorry })
                      (RArray.leaf { hyp := 1189, conc := 1188, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1193, conc := 1192, proof := sorry })
                      (RArray.leaf { hyp := 1203, conc := 1202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1204, conc := 1203, proof := sorry })
                      (RArray.leaf { hyp := 1207, conc := 1205, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1209, conc := 1208, proof := sorry })
                      (RArray.leaf { hyp := 1212, conc := 1210, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1213, conc := 1212, proof := sorry })
                      (RArray.leaf { hyp := 1214, conc := 1213, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1219, conc := 1218, proof := sorry })
                      (RArray.leaf { hyp := 127, conc := 1221, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1325, conc := 131, proof := sorry })
                      (RArray.leaf { hyp := 1328, conc := 1326, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 132, conc := 1328, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1370, conc := 1347, proof := sorry })
                      (RArray.leaf { hyp := 1387, conc := 1381, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1388, conc := 1387, proof := sorry })
                      (RArray.leaf { hyp := 138, conc := 1388, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 139, conc := 1398, proof := sorry })
                      (RArray.leaf { hyp := 142, conc := 1424, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1528, conc := 149, proof := sorry })
                      (RArray.leaf { hyp := 1548, conc := 1547, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1549, conc := 1548, proof := sorry })
                      (RArray.leaf { hyp := 1564, conc := 39, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1573, conc := 1550, proof := sorry })
                      (RArray.leaf { hyp := 1574, conc := 1573, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1577, conc := 1575, proof := sorry })
                      (RArray.leaf { hyp := 1578, conc := 1577, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1582, conc := 1581, proof := sorry })
                      (RArray.leaf { hyp := 1590, conc := 1584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1591, conc := 1590, proof := sorry })
                      (RArray.leaf { hyp := 1594, conc := 1592, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1599, conc := 1598, proof := sorry })
                      (RArray.leaf { hyp := 1603, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1605, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 1609, conc := 1608, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1613, conc := 1611, proof := sorry })
                      (RArray.leaf { hyp := 1614, conc := 1613, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1615, conc := 1614, proof := sorry })
                      (RArray.leaf { hyp := 1619, conc := 1618, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1624, conc := 1623, proof := sorry })
                      (RArray.leaf { hyp := 1625, conc := 1624, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 170, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 1734, conc := 1732, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1742, conc := 1736, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1746, conc := 1744, proof := sorry })
                      (RArray.leaf { hyp := 1750, conc := 1748, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1776, conc := 1753, proof := sorry })
                      (RArray.leaf { hyp := 1780, conc := 1778, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1781, conc := 1780, proof := sorry })
                      (RArray.leaf { hyp := 1784, conc := 1782, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1790, conc := 40, proof := sorry })
                      (RArray.leaf { hyp := 1793, conc := 1787, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1794, conc := 1793, proof := sorry })
                      (RArray.leaf { hyp := 1797, conc := 1795, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1798, conc := 1797, proof := sorry })
                      (RArray.leaf { hyp := 16, conc := 1627, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1801, conc := 1799, proof := sorry })
                      (RArray.leaf { hyp := 1802, conc := 1801, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1803, conc := 1802, proof := sorry })
                      (RArray.leaf { hyp := 179, conc := 17, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1812, conc := 1811, proof := sorry })
                      (RArray.leaf { hyp := 1813, conc := 1812, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1816, conc := 1814, proof := sorry })
                      (RArray.leaf { hyp := 1817, conc := 1816, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1818, conc := 1817, proof := sorry })
                      (RArray.leaf { hyp := 180, conc := 1804, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1821, conc := 1819, proof := sorry })
                      (RArray.leaf { hyp := 1823, conc := 1822, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1826, conc := 1824, proof := sorry })
                      (RArray.leaf { hyp := 1827, conc := 1826, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1828, conc := 1827, proof := sorry })
                      (RArray.leaf { hyp := 1829, conc := 182, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 182, conc := 1828, proof := sorry })
                      (RArray.leaf { hyp := 183, conc := 1830, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 1888, conc := 40, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 1891, conc := 4504, proof := sorry })
                      (RArray.leaf { hyp := 1898, conc := 40, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 17, conc := 1798, proof := sorry })
                      (RArray.leaf { hyp := 190, conc := 184, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 191, conc := 190, proof := sorry })
                      (RArray.leaf { hyp := 1929, conc := 40, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1934, conc := 192, proof := sorry })
                      (RArray.leaf { hyp := 1949, conc := 194, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1950, conc := 1949, proof := sorry })
                      (RArray.leaf { hyp := 1954, conc := 1953, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1955, conc := 1954, proof := sorry })
                      (RArray.leaf { hyp := 194, conc := 1947, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 195, conc := 1956, proof := sorry })
                      (RArray.leaf { hyp := 1977, conc := 318, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1979, conc := 196, proof := sorry })
                      (RArray.leaf { hyp := 1980, conc := 1979, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1983, conc := 1981, proof := sorry })
                      (RArray.leaf { hyp := 1984, conc := 1983, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1987, conc := 1985, proof := sorry })
                      (RArray.leaf { hyp := 1988, conc := 1987, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 1989, conc := 198, proof := sorry })
                      (RArray.leaf { hyp := 1994, conc := 319, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 1996, conc := 1990, proof := sorry })
                      (RArray.leaf { hyp := 198, conc := 1988, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2000, conc := 199, proof := sorry })
                      (RArray.leaf { hyp := 2001, conc := 2000, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2006, conc := 2005, proof := sorry })
                      (RArray.leaf { hyp := 199, conc := 19, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2014, conc := 200, proof := sorry })
                      (RArray.leaf { hyp := 200, conc := 2007, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2019, conc := 201, proof := sorry })
                      (RArray.leaf { hyp := 2020, conc := 2019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2021, conc := 2020, proof := sorry })
                      (RArray.leaf { hyp := 2024, conc := 2022, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2025, conc := 2024, proof := sorry })
                      (RArray.leaf { hyp := 2026, conc := 2025, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2030, conc := 2029, proof := sorry })
                      (RArray.leaf { hyp := 2031, conc := 2030, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2032, conc := 2031, proof := sorry })
                      (RArray.leaf { hyp := 2105, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2137, conc := 20, proof := sorry })
                      (RArray.leaf { hyp := 2145, conc := 3687, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2156, conc := 2154, proof := sorry })
                      (RArray.leaf { hyp := 2176, conc := 40, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2190, conc := 2188, proof := sorry })
                      (RArray.leaf { hyp := 20, conc := 2033, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2199, conc := 21, proof := sorry })
                      (RArray.leaf { hyp := 2207, conc := 2205, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2214, conc := 372, proof := sorry })
                      (RArray.leaf { hyp := 2227, conc := 2225, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2232, conc := 2230, proof := sorry })
                      (RArray.leaf { hyp := 2233, conc := 2232, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2291, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2294, conc := 45, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2297, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2301, conc := 45, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2304, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2311, conc := 45, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2319, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2328, conc := 45, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 231, conc := 2236, proof := sorry })
                      (RArray.leaf { hyp := 2331, conc := 45, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2338, conc := 45, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2351, conc := 234, proof := sorry })
                      (RArray.leaf { hyp := 2352, conc := 2351, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2355, conc := 2353, proof := sorry })
                      (RArray.leaf { hyp := 2356, conc := 2355, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 234, conc := 2345, proof := sorry })
                      (RArray.leaf { hyp := 2360, conc := 2359, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2365, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 235, conc := 2357, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2373, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2385, conc := 236, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2386, conc := 2385, proof := sorry })
                      (RArray.leaf { hyp := 2389, conc := 2387, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2390, conc := 2389, proof := sorry })
                      (RArray.leaf { hyp := 2394, conc := 2393, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2399, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2402, conc := 2396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2403, conc := 2402, proof := sorry })
                      (RArray.leaf { hyp := 2406, conc := 2404, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2407, conc := 2406, proof := sorry })
                      (RArray.leaf { hyp := 2411, conc := 2410, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2420, conc := 2413, proof := sorry })
                      (RArray.leaf { hyp := 2421, conc := 2420, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2422, conc := 2421, proof := sorry })
                      (RArray.leaf { hyp := 2425, conc := 2423, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2426, conc := 2425, proof := sorry })
                      (RArray.leaf { hyp := 2427, conc := 2426, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2430, conc := 242, proof := sorry })
                      (RArray.leaf { hyp := 2431, conc := 2430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2432, conc := 2431, proof := sorry })
                      (RArray.leaf { hyp := 2435, conc := 2433, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2436, conc := 2435, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2437, conc := 2436, proof := sorry })
                      (RArray.leaf { hyp := 2438, conc := 2437, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 242, conc := 2428, proof := sorry })
                      (RArray.leaf { hyp := 2439, conc := 243, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 243, conc := 2438, proof := sorry })
                      (RArray.leaf { hyp := 244, conc := 2439, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2494, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2497, conc := 45, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2500, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2514, conc := 45, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 250, conc := 248, proof := sorry })
                      (RArray.leaf { hyp := 2522, conc := 45, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2531, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2534, conc := 45, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2541, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2543, conc := 253, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2562, conc := 2560, proof := sorry })
                      (RArray.leaf { hyp := 2568, conc := 45, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2576, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2596, conc := 2594, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2602, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2613, conc := 2611, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2623, conc := 2616, proof := sorry })
                      (RArray.leaf { hyp := 2624, conc := 2623, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2625, conc := 2624, proof := sorry })
                      (RArray.leaf { hyp := 2628, conc := 2626, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2633, conc := 2631, proof := sorry })
                      (RArray.leaf { hyp := 2638, conc := 2636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2639, conc := 2638, proof := sorry })
                      (RArray.leaf { hyp := 2710, conc := 3848, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { hyp := 2734, conc := 45, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { hyp := 2737, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2744, conc := 45, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2746, conc := 2642, proof := sorry })
                      (RArray.leaf { hyp := 2757, conc := 2751, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2761, conc := 2759, proof := sorry })
                      (RArray.leaf { hyp := 2762, conc := 2761, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2767, conc := 2766, proof := sorry })
                      (RArray.leaf { hyp := 2791, conc := 2768, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2799, conc := 2797, proof := sorry })
                      (RArray.leaf { hyp := 2808, conc := 2802, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2812, conc := 2810, proof := sorry })
                      (RArray.leaf { hyp := 2813, conc := 2812, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2818, conc := 2817, proof := sorry })
                      (RArray.leaf { hyp := 2826, conc := 2819, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2831, conc := 2829, proof := sorry })
                      (RArray.leaf { hyp := 2832, conc := 2831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2833, conc := 2832, proof := sorry })
                      (RArray.leaf { hyp := 2836, conc := 2834, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2837, conc := 2836, proof := sorry })
                      (RArray.leaf { hyp := 2838, conc := 2837, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2842, conc := 2841, proof := sorry })
                      (RArray.leaf { hyp := 2844, conc := 2843, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 283, conc := 2838, proof := sorry })
                      (RArray.leaf { hyp := 284, conc := 2845, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 286, conc := 284, proof := sorry })
                      (RArray.leaf { hyp := 287, conc := 286, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2903, conc := 45, proof := sorry })
                      (RArray.leaf { hyp := 2949, conc := 294, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 294, conc := 288, proof := sorry })
                      (RArray.leaf { hyp := 2960, conc := 295, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2968, conc := 2966, proof := sorry })
                      (RArray.leaf { hyp := 295, conc := 2954, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2969, conc := 296, proof := sorry })
                      (RArray.leaf { hyp := 2970, conc := 2969, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2994, conc := 298, proof := sorry })
                      (RArray.leaf { hyp := 2995, conc := 2994, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 2998, conc := 2996, proof := sorry })
                      (RArray.leaf { hyp := 298, conc := 2971, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 2999, conc := 299, proof := sorry })
                      (RArray.leaf { hyp := 3003, conc := 3002, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 299, conc := 2998, proof := sorry })
                      (RArray.leaf { hyp := 3011, conc := 300, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3012, conc := 3011, proof := sorry })
                      (RArray.leaf { hyp := 3015, conc := 3013, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3016, conc := 3015, proof := sorry })
                      (RArray.leaf { hyp := 3020, conc := 3019, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3029, conc := 302, proof := sorry })
                      (RArray.leaf { hyp := 3030, conc := 3029, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3031, conc := 3030, proof := sorry })
                      (RArray.leaf { hyp := 3034, conc := 3032, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3035, conc := 3034, proof := sorry })
                      (RArray.leaf { hyp := 3036, conc := 3035, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 302, conc := 3022, proof := sorry })
                      (RArray.leaf { hyp := 3039, conc := 303, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3045, conc := 3044, proof := sorry })
                      (RArray.leaf { hyp := 3046, conc := 3045, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3047, conc := 3046, proof := sorry })
                      (RArray.leaf { hyp := 304, conc := 3048, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { hyp := 3120, conc := 4693, proof := sorry })
                      (RArray.leaf { hyp := 3124, conc := 45, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { hyp := 3147, conc := 4693, proof := sorry })
                      (RArray.leaf { hyp := 3152, conc := 305, proof := sorry })))))))))))

end EndToEnd
