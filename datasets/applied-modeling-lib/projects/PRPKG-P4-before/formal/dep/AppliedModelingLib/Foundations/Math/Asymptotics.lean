import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

open Asymptotics

open scoped BigOperators

namespace AppliedModelingLib

namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0)

/-- `x n` is asymptotically equivalent to `y n`, expressed as `x n / y n -> 1`. -/
def AsymptoticEquivalent (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n / y n) atTop (nhds 1)

namespace AsymptoticEquivalent

end AsymptoticEquivalent

end Math

end AppliedModelingLib
