import Mathlib.Data.Real.Basic
import Mathlib.Topology.Closure

structure loop (X : Type*) where
  to_fun : ℝ → X
  per' : ∀ t, to_fun (t + 1) = to_fun t

instance {X : Type*} : CoeFun (loop X) (fun _ => ℝ → X) := ⟨loop.to_fun⟩

namespace loop

variable {X X' : Type*}

def is_const (γ : loop X) := ∀ t s, γ t = γ s

variable [TopologicalSpace X] [TopologicalSpace X']

def support (γ : X → loop X') : Set X :=
  closure {x | ¬ (γ x).is_const}

end loop
