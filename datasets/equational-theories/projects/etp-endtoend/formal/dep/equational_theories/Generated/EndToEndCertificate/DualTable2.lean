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
def _root_.EndToEnd.dualtable2 : RArray EndToEnd.DualFact :=
RArray.branch 347
  (RArray.branch 173
    (RArray.branch 86
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4000, dual := 3534, proof := sorry })
                  (RArray.leaf { law := 4001, dual := 3639, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4002, dual := 3622, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4003, dual := 3641, proof := sorry })
                    (RArray.leaf { law := 4004, dual := 3556, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4005, dual := 3519, proof := sorry })
                  (RArray.leaf { law := 4006, dual := 3600, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4007, dual := 3601, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4008, dual := 3546, proof := sorry })
                    (RArray.leaf { law := 4009, dual := 3509, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4010, dual := 3583, proof := sorry })
                  (RArray.leaf { law := 4011, dual := 3584, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4012, dual := 3566, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4013, dual := 3529, proof := sorry })
                    (RArray.leaf { law := 4014, dual := 3617, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4015, dual := 3635, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4016, dual := 3567, proof := sorry })
                    (RArray.leaf { law := 4017, dual := 3530, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4018, dual := 3634, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4019, dual := 3618, proof := sorry })
                    (RArray.leaf { law := 4020, dual := 3636, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4021, dual := 3562, proof := sorry })
                  (RArray.leaf { law := 4022, dual := 3525, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4023, dual := 3608, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4024, dual := 3613, proof := sorry })
                    (RArray.leaf { law := 4025, dual := 3552, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4026, dual := 3515, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4027, dual := 3591, proof := sorry })
                    (RArray.leaf { law := 4028, dual := 3596, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4029, dual := 3574, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4030, dual := 3537, proof := sorry })
                    (RArray.leaf { law := 4031, dual := 3625, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4032, dual := 3650, proof := sorry })
                  (RArray.leaf { law := 4033, dual := 3579, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4034, dual := 3542, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4035, dual := 3644, proof := sorry })
                    (RArray.leaf { law := 4036, dual := 3630, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4037, dual := 3656, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4038, dual := 3563, proof := sorry })
                    (RArray.leaf { law := 4039, dual := 3526, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4040, dual := 3612, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4041, dual := 3609, proof := sorry })
                    (RArray.leaf { law := 4042, dual := 3614, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4043, dual := 3553, proof := sorry })
                  (RArray.leaf { law := 4044, dual := 3516, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4045, dual := 3595, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4046, dual := 3592, proof := sorry })
                    (RArray.leaf { law := 4047, dual := 3597, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4048, dual := 3578, proof := sorry })
                  (RArray.leaf { law := 4049, dual := 3541, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4050, dual := 3629, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4051, dual := 3645, proof := sorry })
                    (RArray.leaf { law := 4052, dual := 3655, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4053, dual := 3575, proof := sorry })
                  (RArray.leaf { law := 4054, dual := 3538, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4055, dual := 3649, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4056, dual := 3626, proof := sorry })
                    (RArray.leaf { law := 4057, dual := 3651, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4058, dual := 3580, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4059, dual := 3543, proof := sorry })
                    (RArray.leaf { law := 4060, dual := 3654, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4061, dual := 3646, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4062, dual := 3631, proof := sorry })
                    (RArray.leaf { law := 4063, dual := 3657, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4064, dual := 3252, proof := sorry })
                  (RArray.leaf { law := 4065, dual := 3267, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4066, dual := 3257, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4067, dual := 3277, proof := sorry })
                    (RArray.leaf { law := 4068, dual := 3287, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4069, dual := 3254, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4070, dual := 3270, proof := sorry })
                    (RArray.leaf { law := 4071, dual := 3273, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4072, dual := 3260, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4073, dual := 3280, proof := sorry })
                    (RArray.leaf { law := 4074, dual := 3295, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4075, dual := 3263, proof := sorry })
                  (RArray.leaf { law := 4076, dual := 3291, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4077, dual := 3283, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4078, dual := 3299, proof := sorry })
                    (RArray.leaf { law := 4079, dual := 3253, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4080, dual := 3268, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4081, dual := 3269, proof := sorry })
                    (RArray.leaf { law := 4082, dual := 3258, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4083, dual := 3278, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4084, dual := 3289, proof := sorry })
                    (RArray.leaf { law := 4085, dual := 3259, proof := sorry }))))))))
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4086, dual := 3288, proof := sorry })
                  (RArray.leaf { law := 4087, dual := 3279, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4088, dual := 3290, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4089, dual := 3255, proof := sorry })
                    (RArray.leaf { law := 4090, dual := 3271, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4091, dual := 3275, proof := sorry })
                  (RArray.leaf { law := 4092, dual := 3261, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4093, dual := 3281, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4094, dual := 3297, proof := sorry })
                    (RArray.leaf { law := 4095, dual := 3265, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4096, dual := 3292, proof := sorry })
                  (RArray.leaf { law := 4097, dual := 3285, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4098, dual := 3302, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4099, dual := 3256, proof := sorry })
                    (RArray.leaf { law := 4100, dual := 3274, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4101, dual := 3272, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4102, dual := 3276, proof := sorry })
                    (RArray.leaf { law := 4103, dual := 3264, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4104, dual := 3284, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4105, dual := 3293, proof := sorry })
                    (RArray.leaf { law := 4106, dual := 3301, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4107, dual := 3262, proof := sorry })
                  (RArray.leaf { law := 4108, dual := 3296, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4109, dual := 3282, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4110, dual := 3298, proof := sorry })
                    (RArray.leaf { law := 4111, dual := 3266, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4112, dual := 3300, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4113, dual := 3294, proof := sorry })
                    (RArray.leaf { law := 4114, dual := 3286, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4115, dual := 3303, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4116, dual := 3355, proof := sorry })
                    (RArray.leaf { law := 4117, dual := 3318, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4118, dual := 3400, proof := sorry })
                  (RArray.leaf { law := 4119, dual := 3345, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4120, dual := 3308, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4121, dual := 3383, proof := sorry })
                    (RArray.leaf { law := 4122, dual := 3366, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4123, dual := 3329, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4124, dual := 3417, proof := sorry })
                    (RArray.leaf { law := 4125, dual := 3435, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4126, dual := 3352, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4127, dual := 3315, proof := sorry })
                    (RArray.leaf { law := 4128, dual := 3396, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4129, dual := 3342, proof := sorry })
                  (RArray.leaf { law := 4130, dual := 3305, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4131, dual := 3379, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4132, dual := 3362, proof := sorry })
                    (RArray.leaf { law := 4133, dual := 3325, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4134, dual := 3413, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4135, dual := 3430, proof := sorry })
                    (RArray.leaf { law := 4136, dual := 3358, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4137, dual := 3321, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4138, dual := 3404, proof := sorry })
                    (RArray.leaf { law := 4139, dual := 3408, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4140, dual := 3348, proof := sorry })
                  (RArray.leaf { law := 4141, dual := 3311, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4142, dual := 3387, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4143, dual := 3391, proof := sorry })
                    (RArray.leaf { law := 4144, dual := 3370, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4145, dual := 3333, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4146, dual := 3421, proof := sorry })
                    (RArray.leaf { law := 4147, dual := 3445, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4148, dual := 3374, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4149, dual := 3337, proof := sorry })
                    (RArray.leaf { law := 4150, dual := 3440, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4151, dual := 3425, proof := sorry })
                  (RArray.leaf { law := 4152, dual := 3450, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4153, dual := 3354, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4154, dual := 3317, proof := sorry })
                    (RArray.leaf { law := 4155, dual := 3399, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4156, dual := 3344, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4157, dual := 3307, proof := sorry })
                    (RArray.leaf { law := 4158, dual := 3382, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4159, dual := 3365, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4160, dual := 3328, proof := sorry })
                    (RArray.leaf { law := 4161, dual := 3416, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4162, dual := 3434, proof := sorry })
                  (RArray.leaf { law := 4163, dual := 3351, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4164, dual := 3314, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4165, dual := 3395, proof := sorry })
                    (RArray.leaf { law := 4166, dual := 3341, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4167, dual := 3304, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4168, dual := 3378, proof := sorry })
                    (RArray.leaf { law := 4169, dual := 3361, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4170, dual := 3324, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4171, dual := 3412, proof := sorry })
                    (RArray.leaf { law := 4172, dual := 3429, proof := sorry })))))))))
    (RArray.branch 87
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4173, dual := 3357, proof := sorry })
                  (RArray.leaf { law := 4174, dual := 3320, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4175, dual := 3403, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4176, dual := 3407, proof := sorry })
                    (RArray.leaf { law := 4177, dual := 3347, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4178, dual := 3310, proof := sorry })
                  (RArray.leaf { law := 4179, dual := 3386, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4180, dual := 3390, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4181, dual := 3369, proof := sorry })
                    (RArray.leaf { law := 4182, dual := 3332, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4183, dual := 3420, proof := sorry })
                  (RArray.leaf { law := 4184, dual := 3444, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4185, dual := 3373, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4186, dual := 3336, proof := sorry })
                    (RArray.leaf { law := 4187, dual := 3439, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4188, dual := 3424, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4189, dual := 3449, proof := sorry })
                    (RArray.leaf { law := 4190, dual := 3356, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4191, dual := 3319, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4192, dual := 3401, proof := sorry })
                    (RArray.leaf { law := 4193, dual := 3402, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4194, dual := 3346, proof := sorry })
                  (RArray.leaf { law := 4195, dual := 3309, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4196, dual := 3384, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4197, dual := 3385, proof := sorry })
                    (RArray.leaf { law := 4198, dual := 3367, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4199, dual := 3330, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4200, dual := 3418, proof := sorry })
                    (RArray.leaf { law := 4201, dual := 3437, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4202, dual := 3368, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4203, dual := 3331, proof := sorry })
                    (RArray.leaf { law := 4204, dual := 3436, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4205, dual := 3419, proof := sorry })
                  (RArray.leaf { law := 4206, dual := 3438, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4207, dual := 3353, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4208, dual := 3316, proof := sorry })
                    (RArray.leaf { law := 4209, dual := 3397, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4210, dual := 3398, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4211, dual := 3343, proof := sorry })
                    (RArray.leaf { law := 4212, dual := 3306, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4213, dual := 3380, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4214, dual := 3381, proof := sorry })
                    (RArray.leaf { law := 4215, dual := 3363, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4216, dual := 3326, proof := sorry })
                  (RArray.leaf { law := 4217, dual := 3414, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4218, dual := 3432, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4219, dual := 3364, proof := sorry })
                    (RArray.leaf { law := 4220, dual := 3327, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4221, dual := 3431, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4222, dual := 3415, proof := sorry })
                    (RArray.leaf { law := 4223, dual := 3433, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4224, dual := 3359, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4225, dual := 3322, proof := sorry })
                    (RArray.leaf { law := 4226, dual := 3405, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4227, dual := 3410, proof := sorry })
                  (RArray.leaf { law := 4228, dual := 3349, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4229, dual := 3312, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4230, dual := 3388, proof := sorry })
                    (RArray.leaf { law := 4231, dual := 3393, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4232, dual := 3371, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4233, dual := 3334, proof := sorry })
                    (RArray.leaf { law := 4234, dual := 3422, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4235, dual := 3447, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4236, dual := 3376, proof := sorry })
                    (RArray.leaf { law := 4237, dual := 3339, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4238, dual := 3441, proof := sorry })
                  (RArray.leaf { law := 4239, dual := 3427, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4240, dual := 3453, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4241, dual := 3360, proof := sorry })
                    (RArray.leaf { law := 4242, dual := 3323, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4243, dual := 3409, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4244, dual := 3406, proof := sorry })
                    (RArray.leaf { law := 4245, dual := 3411, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4246, dual := 3350, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4247, dual := 3313, proof := sorry })
                    (RArray.leaf { law := 4248, dual := 3392, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4249, dual := 3389, proof := sorry })
                  (RArray.leaf { law := 4250, dual := 3394, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4251, dual := 3375, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4252, dual := 3338, proof := sorry })
                    (RArray.leaf { law := 4253, dual := 3426, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4254, dual := 3442, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4255, dual := 3452, proof := sorry })
                    (RArray.leaf { law := 4256, dual := 3372, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4257, dual := 3335, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4258, dual := 3446, proof := sorry })
                    (RArray.leaf { law := 4259, dual := 3423, proof := sorry }))))))))
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4260, dual := 3448, proof := sorry })
                  (RArray.leaf { law := 4261, dual := 3377, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4262, dual := 3340, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4263, dual := 3451, proof := sorry })
                    (RArray.leaf { law := 4264, dual := 3443, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4265, dual := 3428, proof := sorry })
                  (RArray.leaf { law := 4266, dual := 3454, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4267, dual := 4586, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4268, dual := 4583, proof := sorry })
                    (RArray.leaf { law := 4269, dual := 4589, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4270, dual := 4592, proof := sorry })
                  (RArray.leaf { law := 4271, dual := 4582, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4272, dual := 4587, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4273, dual := 4588, proof := sorry })
                    (RArray.leaf { law := 4274, dual := 4584, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4275, dual := 4590, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4276, dual := 4594, proof := sorry })
                    (RArray.leaf { law := 4277, dual := 4585, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4278, dual := 4593, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4279, dual := 4591, proof := sorry })
                    (RArray.leaf { law := 4280, dual := 4595, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4281, dual := 4665, proof := sorry })
                  (RArray.leaf { law := 4282, dual := 4634, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4283, dual := 4598, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4284, dual := 4662, proof := sorry })
                    (RArray.leaf { law := 4285, dual := 4641, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4286, dual := 4654, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4287, dual := 4618, proof := sorry })
                    (RArray.leaf { law := 4288, dual := 4668, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4289, dual := 4604, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4290, dual := 4628, proof := sorry })
                    (RArray.leaf { law := 4291, dual := 4664, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4292, dual := 4657, proof := sorry })
                  (RArray.leaf { law := 4293, dual := 4660, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4294, dual := 4659, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4295, dual := 4632, proof := sorry })
                    (RArray.leaf { law := 4296, dual := 4611, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4297, dual := 4667, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4298, dual := 4613, proof := sorry })
                    (RArray.leaf { law := 4299, dual := 4653, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4300, dual := 4645, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4301, dual := 4666, proof := sorry })
                    (RArray.leaf { law := 4302, dual := 4658, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4303, dual := 4602, proof := sorry })
                  (RArray.leaf { law := 4304, dual := 4639, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4305, dual := 4663, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4306, dual := 4655, proof := sorry })
                    (RArray.leaf { law := 4307, dual := 4669, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4308, dual := 4661, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4309, dual := 4656, proof := sorry })
                    (RArray.leaf { law := 4310, dual := 4651, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4311, dual := 4626, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4312, dual := 4670, proof := sorry })
                    (RArray.leaf { law := 4313, dual := 4605, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4314, dual := 4644, proof := sorry })
                  (RArray.leaf { law := 4315, dual := 4630, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4316, dual := 4637, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4317, dual := 4610, proof := sorry })
                    (RArray.leaf { law := 4318, dual := 4648, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4319, dual := 4597, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4320, dual := 4635, proof := sorry })
                    (RArray.leaf { law := 4321, dual := 4642, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4322, dual := 4631, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4323, dual := 4638, proof := sorry })
                    (RArray.leaf { law := 4324, dual := 4619, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4325, dual := 4649, proof := sorry })
                  (RArray.leaf { law := 4326, dual := 4600, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4327, dual := 4636, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4328, dual := 4643, proof := sorry })
                    (RArray.leaf { law := 4329, dual := 4629, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4330, dual := 4615, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4331, dual := 4646, proof := sorry })
                    (RArray.leaf { law := 4332, dual := 4647, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4333, dual := 4633, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4334, dual := 4640, proof := sorry })
                    (RArray.leaf { law := 4335, dual := 4650, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4336, dual := 4625, proof := sorry })
                  (RArray.leaf { law := 4337, dual := 4652, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4338, dual := 4614, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4339, dual := 4601, proof := sorry })
                    (RArray.leaf { law := 4340, dual := 4621, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4341, dual := 4624, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4342, dual := 4607, proof := sorry })
                    (RArray.leaf { law := 4343, dual := 4617, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4344, dual := 4609, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4345, dual := 4608, proof := sorry })
                    (RArray.leaf { law := 4346, dual := 4623, proof := sorry }))))))))))
  (RArray.branch 173
    (RArray.branch 86
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4347, dual := 4599, proof := sorry })
                  (RArray.leaf { law := 4348, dual := 4620, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4349, dual := 4606, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4350, dual := 4596, proof := sorry })
                    (RArray.leaf { law := 4351, dual := 4616, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4352, dual := 4612, proof := sorry })
                  (RArray.leaf { law := 4353, dual := 4603, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4354, dual := 4622, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4355, dual := 4627, proof := sorry })
                    (RArray.leaf { law := 4356, dual := 4688, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4357, dual := 4676, proof := sorry })
                  (RArray.leaf { law := 4358, dual := 4681, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4359, dual := 4674, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4360, dual := 4692, proof := sorry })
                    (RArray.leaf { law := 4361, dual := 4672, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4362, dual := 4690, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4363, dual := 4678, proof := sorry })
                    (RArray.leaf { law := 4364, dual := 4679, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4365, dual := 4686, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4366, dual := 4673, proof := sorry })
                    (RArray.leaf { law := 4367, dual := 4691, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4368, dual := 4683, proof := sorry })
                  (RArray.leaf { law := 4369, dual := 4684, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4370, dual := 4685, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4371, dual := 4680, proof := sorry })
                    (RArray.leaf { law := 4372, dual := 4687, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4373, dual := 4671, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4374, dual := 4689, proof := sorry })
                    (RArray.leaf { law := 4375, dual := 4677, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4376, dual := 4682, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4377, dual := 4675, proof := sorry })
                    (RArray.leaf { law := 4378, dual := 4693, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4379, dual := 4379, proof := sorry })
                  (RArray.leaf { law := 4380, dual := 4482, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4381, dual := 4431, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4382, dual := 4408, proof := sorry })
                    (RArray.leaf { law := 4383, dual := 4549, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4384, dual := 4394, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4385, dual := 4445, proof := sorry })
                    (RArray.leaf { law := 4386, dual := 4527, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4387, dual := 4468, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4388, dual := 4388, proof := sorry })
                    (RArray.leaf { law := 4389, dual := 4498, proof := sorry })))))))
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4390, dual := 4505, proof := sorry })
                  (RArray.leaf { law := 4391, dual := 4461, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4392, dual := 4424, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4393, dual := 4574, proof := sorry })
                    (RArray.leaf { law := 4394, dual := 4384, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4395, dual := 4472, proof := sorry })
                  (RArray.leaf { law := 4396, dual := 4493, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4397, dual := 4441, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4398, dual := 4398, proof := sorry })
                    (RArray.leaf { law := 4399, dual := 4532, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4400, dual := 4451, proof := sorry })
                  (RArray.leaf { law := 4401, dual := 4515, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4402, dual := 4419, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4403, dual := 4568, proof := sorry })
                    (RArray.leaf { law := 4404, dual := 4404, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4405, dual := 4435, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4406, dual := 4544, proof := sorry })
                    (RArray.leaf { law := 4407, dual := 4478, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4408, dual := 4382, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4409, dual := 4486, proof := sorry })
                    (RArray.leaf { law := 4410, dual := 4539, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4411, dual := 4439, proof := sorry })
                  (RArray.leaf { law := 4412, dual := 4412, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4413, dual := 4554, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4414, dual := 4414, proof := sorry })
                    (RArray.leaf { law := 4415, dual := 4510, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4416, dual := 4456, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4417, dual := 4562, proof := sorry })
                    (RArray.leaf { law := 4418, dual := 4522, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4419, dual := 4402, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4420, dual := 4449, proof := sorry })
                    (RArray.leaf { law := 4421, dual := 4537, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4422, dual := 4488, proof := sorry })
                  (RArray.leaf { law := 4423, dual := 4476, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4424, dual := 4392, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4425, dual := 4503, proof := sorry })
                    (RArray.leaf { law := 4426, dual := 4556, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4427, dual := 4520, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4428, dual := 4466, proof := sorry })
                    (RArray.leaf { law := 4429, dual := 4429, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4430, dual := 4580, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4431, dual := 4381, proof := sorry })
                    (RArray.leaf { law := 4432, dual := 4479, proof := sorry }))))))))
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4433, dual := 4485, proof := sorry })
                  (RArray.leaf { law := 4434, dual := 4434, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4435, dual := 4405, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4436, dual := 4545, proof := sorry })
                    (RArray.leaf { law := 4437, dual := 4437, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4438, dual := 4541, proof := sorry })
                  (RArray.leaf { law := 4439, dual := 4411, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4440, dual := 4553, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4441, dual := 4397, proof := sorry })
                    (RArray.leaf { law := 4442, dual := 4442, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4443, dual := 4531, proof := sorry })
                  (RArray.leaf { law := 4444, dual := 4471, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4445, dual := 4385, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4446, dual := 4494, proof := sorry })
                    (RArray.leaf { law := 4447, dual := 4513, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4448, dual := 4453, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4449, dual := 4420, proof := sorry })
                    (RArray.leaf { law := 4450, dual := 4569, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4451, dual := 4400, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4452, dual := 4523, proof := sorry })
                    (RArray.leaf { law := 4453, dual := 4448, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4454, dual := 4535, proof := sorry })
                  (RArray.leaf { law := 4455, dual := 4509, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4456, dual := 4416, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4457, dual := 4457, proof := sorry })
                    (RArray.leaf { law := 4458, dual := 4564, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4459, dual := 4474, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4460, dual := 4490, proof := sorry })
                    (RArray.leaf { law := 4461, dual := 4391, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4462, dual := 4502, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4463, dual := 4517, proof := sorry })
                    (RArray.leaf { law := 4464, dual := 4559, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4465, dual := 4465, proof := sorry })
                  (RArray.leaf { law := 4466, dual := 4428, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4467, dual := 4579, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4468, dual := 4387, proof := sorry })
                    (RArray.leaf { law := 4469, dual := 4469, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4470, dual := 4497, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4471, dual := 4444, proof := sorry })
                    (RArray.leaf { law := 4472, dual := 4395, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4473, dual := 4528, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4474, dual := 4459, proof := sorry })
                    (RArray.leaf { law := 4475, dual := 4507, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4476, dual := 4423, proof := sorry })
                  (RArray.leaf { law := 4477, dual := 4573, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4478, dual := 4407, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4479, dual := 4432, proof := sorry })
                    (RArray.leaf { law := 4480, dual := 4548, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4481, dual := 4481, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4482, dual := 4380, proof := sorry })
                    (RArray.leaf { law := 4483, dual := 4483, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4484, dual := 4547, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4485, dual := 4433, proof := sorry })
                    (RArray.leaf { law := 4486, dual := 4409, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4487, dual := 4550, proof := sorry })
                  (RArray.leaf { law := 4488, dual := 4422, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4489, dual := 4506, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4490, dual := 4460, proof := sorry })
                    (RArray.leaf { law := 4491, dual := 4572, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4492, dual := 4526, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4493, dual := 4396, proof := sorry })
                    (RArray.leaf { law := 4494, dual := 4446, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4495, dual := 4529, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4496, dual := 4496, proof := sorry })
                    (RArray.leaf { law := 4497, dual := 4470, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4498, dual := 4389, proof := sorry })
                  (RArray.leaf { law := 4499, dual := 4499, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4500, dual := 4571, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4501, dual := 4508, proof := sorry })
                    (RArray.leaf { law := 4502, dual := 4462, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4503, dual := 4425, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4504, dual := 4575, proof := sorry })
                    (RArray.leaf { law := 4505, dual := 4390, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4506, dual := 4489, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4507, dual := 4475, proof := sorry })
                    (RArray.leaf { law := 4508, dual := 4501, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4509, dual := 4455, proof := sorry })
                  (RArray.leaf { law := 4510, dual := 4415, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4511, dual := 4511, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4512, dual := 4563, proof := sorry })
                    (RArray.leaf { law := 4513, dual := 4447, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4514, dual := 4524, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4515, dual := 4401, proof := sorry })
                    (RArray.leaf { law := 4516, dual := 4536, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4517, dual := 4463, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4518, dual := 4558, proof := sorry })
                    (RArray.leaf { law := 4519, dual := 4519, proof := sorry })))))))))
    (RArray.branch 87
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4520, dual := 4427, proof := sorry })
                  (RArray.leaf { law := 4521, dual := 4578, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4522, dual := 4418, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4523, dual := 4452, proof := sorry })
                    (RArray.leaf { law := 4524, dual := 4514, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4525, dual := 4567, proof := sorry })
                  (RArray.leaf { law := 4526, dual := 4492, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4527, dual := 4386, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4528, dual := 4473, proof := sorry })
                    (RArray.leaf { law := 4529, dual := 4495, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4530, dual := 4530, proof := sorry })
                  (RArray.leaf { law := 4531, dual := 4443, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4532, dual := 4399, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4533, dual := 4533, proof := sorry })
                    (RArray.leaf { law := 4534, dual := 4566, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4535, dual := 4454, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4536, dual := 4516, proof := sorry })
                    (RArray.leaf { law := 4537, dual := 4421, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4538, dual := 4570, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4539, dual := 4410, proof := sorry })
                    (RArray.leaf { law := 4540, dual := 4540, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4541, dual := 4438, proof := sorry })
                  (RArray.leaf { law := 4542, dual := 4552, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4543, dual := 4543, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4544, dual := 4406, proof := sorry })
                    (RArray.leaf { law := 4545, dual := 4436, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4546, dual := 4546, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4547, dual := 4484, proof := sorry })
                    (RArray.leaf { law := 4548, dual := 4480, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4549, dual := 4383, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4550, dual := 4487, proof := sorry })
                    (RArray.leaf { law := 4551, dual := 4551, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4552, dual := 4542, proof := sorry })
                  (RArray.leaf { law := 4553, dual := 4440, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4554, dual := 4413, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4555, dual := 4555, proof := sorry })
                    (RArray.leaf { law := 4556, dual := 4426, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4557, dual := 4557, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4558, dual := 4518, proof := sorry })
                    (RArray.leaf { law := 4559, dual := 4464, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4560, dual := 4577, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4561, dual := 4561, proof := sorry })
                    (RArray.leaf { law := 4562, dual := 4417, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4563, dual := 4512, proof := sorry })
                  (RArray.leaf { law := 4564, dual := 4458, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4565, dual := 4565, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4566, dual := 4534, proof := sorry })
                    (RArray.leaf { law := 4567, dual := 4525, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4568, dual := 4403, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4569, dual := 4450, proof := sorry })
                    (RArray.leaf { law := 4570, dual := 4538, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4571, dual := 4500, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4572, dual := 4491, proof := sorry })
                    (RArray.leaf { law := 4573, dual := 4477, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4574, dual := 4393, proof := sorry })
                  (RArray.leaf { law := 4575, dual := 4504, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4576, dual := 4576, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4577, dual := 4560, proof := sorry })
                    (RArray.leaf { law := 4578, dual := 4521, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4579, dual := 4467, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4580, dual := 4430, proof := sorry })
                    (RArray.leaf { law := 4581, dual := 4581, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4582, dual := 4271, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4583, dual := 4268, proof := sorry })
                    (RArray.leaf { law := 4584, dual := 4274, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4585, dual := 4277, proof := sorry })
                  (RArray.leaf { law := 4586, dual := 4267, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4587, dual := 4272, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4588, dual := 4273, proof := sorry })
                    (RArray.leaf { law := 4589, dual := 4269, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4590, dual := 4275, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4591, dual := 4279, proof := sorry })
                    (RArray.leaf { law := 4592, dual := 4270, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4593, dual := 4278, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4594, dual := 4276, proof := sorry })
                    (RArray.leaf { law := 4595, dual := 4280, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4596, dual := 4350, proof := sorry })
                  (RArray.leaf { law := 4597, dual := 4319, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4598, dual := 4283, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4599, dual := 4347, proof := sorry })
                    (RArray.leaf { law := 4600, dual := 4326, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4601, dual := 4339, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4602, dual := 4303, proof := sorry })
                    (RArray.leaf { law := 4603, dual := 4353, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4604, dual := 4289, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4605, dual := 4313, proof := sorry })
                    (RArray.leaf { law := 4606, dual := 4349, proof := sorry }))))))))
      (RArray.branch 43
        (RArray.branch 21
          (RArray.branch 10
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4607, dual := 4342, proof := sorry })
                  (RArray.leaf { law := 4608, dual := 4345, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4609, dual := 4344, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4610, dual := 4317, proof := sorry })
                    (RArray.leaf { law := 4611, dual := 4296, proof := sorry }))))
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4612, dual := 4352, proof := sorry })
                  (RArray.leaf { law := 4613, dual := 4298, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4614, dual := 4338, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4615, dual := 4330, proof := sorry })
                    (RArray.leaf { law := 4616, dual := 4351, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4617, dual := 4343, proof := sorry })
                  (RArray.leaf { law := 4618, dual := 4287, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4619, dual := 4324, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4620, dual := 4348, proof := sorry })
                    (RArray.leaf { law := 4621, dual := 4340, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4622, dual := 4354, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4623, dual := 4346, proof := sorry })
                    (RArray.leaf { law := 4624, dual := 4341, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4625, dual := 4336, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4626, dual := 4311, proof := sorry })
                    (RArray.leaf { law := 4627, dual := 4355, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4628, dual := 4290, proof := sorry })
                  (RArray.leaf { law := 4629, dual := 4329, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4630, dual := 4315, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4631, dual := 4322, proof := sorry })
                    (RArray.leaf { law := 4632, dual := 4295, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4633, dual := 4333, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4634, dual := 4282, proof := sorry })
                    (RArray.leaf { law := 4635, dual := 4320, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4636, dual := 4327, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4637, dual := 4316, proof := sorry })
                    (RArray.leaf { law := 4638, dual := 4323, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4639, dual := 4304, proof := sorry })
                  (RArray.leaf { law := 4640, dual := 4334, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4641, dual := 4285, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4642, dual := 4321, proof := sorry })
                    (RArray.leaf { law := 4643, dual := 4328, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4644, dual := 4314, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4645, dual := 4300, proof := sorry })
                    (RArray.leaf { law := 4646, dual := 4331, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4647, dual := 4332, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4648, dual := 4318, proof := sorry })
                    (RArray.leaf { law := 4649, dual := 4325, proof := sorry })))))))
        (RArray.branch 22
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4650, dual := 4335, proof := sorry })
                  (RArray.leaf { law := 4651, dual := 4310, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4652, dual := 4337, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4653, dual := 4299, proof := sorry })
                    (RArray.leaf { law := 4654, dual := 4286, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4655, dual := 4306, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4656, dual := 4309, proof := sorry })
                    (RArray.leaf { law := 4657, dual := 4292, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4658, dual := 4302, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4659, dual := 4294, proof := sorry })
                    (RArray.leaf { law := 4660, dual := 4293, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4661, dual := 4308, proof := sorry })
                  (RArray.leaf { law := 4662, dual := 4284, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4663, dual := 4305, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4664, dual := 4291, proof := sorry })
                    (RArray.leaf { law := 4665, dual := 4281, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4666, dual := 4301, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4667, dual := 4297, proof := sorry })
                    (RArray.leaf { law := 4668, dual := 4288, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4669, dual := 4307, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4670, dual := 4312, proof := sorry })
                    (RArray.leaf { law := 4671, dual := 4373, proof := sorry }))))))
          (RArray.branch 11
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4672, dual := 4361, proof := sorry })
                  (RArray.leaf { law := 4673, dual := 4366, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4674, dual := 4359, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4675, dual := 4377, proof := sorry })
                    (RArray.leaf { law := 4676, dual := 4357, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4677, dual := 4375, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4678, dual := 4363, proof := sorry })
                    (RArray.leaf { law := 4679, dual := 4364, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4680, dual := 4371, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4681, dual := 4358, proof := sorry })
                    (RArray.leaf { law := 4682, dual := 4376, proof := sorry })))))
            (RArray.branch 5
              (RArray.branch 2
                (RArray.branch 1 (RArray.leaf { law := 4683, dual := 4368, proof := sorry })
                  (RArray.leaf { law := 4684, dual := 4369, proof := sorry }))
                (RArray.branch 1 (RArray.leaf { law := 4685, dual := 4370, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4686, dual := 4365, proof := sorry })
                    (RArray.leaf { law := 4687, dual := 4372, proof := sorry }))))
              (RArray.branch 3
                (RArray.branch 1 (RArray.leaf { law := 4688, dual := 4356, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4689, dual := 4374, proof := sorry })
                    (RArray.leaf { law := 4690, dual := 4362, proof := sorry })))
                (RArray.branch 1 (RArray.leaf { law := 4691, dual := 4367, proof := sorry })
                  (RArray.branch 1 (RArray.leaf { law := 4692, dual := 4360, proof := sorry })
                    (RArray.leaf { law := 4693, dual := 4378, proof := sorry }))))))))))

end EndToEnd
