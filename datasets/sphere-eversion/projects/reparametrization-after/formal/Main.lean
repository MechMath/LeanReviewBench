import Mathlib
import dep.Common

noncomputable section

open Set Function MeasureTheory

open scoped ContDiff Topology

structure equivariant_equiv extends Equiv ℝ ℝ where
  map_zero' : toFun 0 = 0
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1

instance : CoeFun equivariant_equiv (fun _ => ℝ → ℝ) := ⟨fun e => e.toFun⟩

namespace equivariant_equiv

def symm (e : equivariant_equiv) : equivariant_equiv where
  toEquiv := e.toEquiv.symm
  map_zero' := sorry
  eqv' t := sorry

end equivariant_equiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

def loop.reparam (γ : loop F) (φ : equivariant_equiv) : loop F where
  to_fun := γ ∘ φ
  per' t := sorry

structure smooth_surrounding_family (g : E → F) where
  to_fun : E → loop F
  smooth : ∀ x s, smooth_at (fun p : E × ℝ => to_fun p.1 p.2) (x, s)
  surrounds : ∀ x, (to_fun x).surrounds (g x)

namespace smooth_surrounding_family

variable {g : E → F}

instance : CoeFun (smooth_surrounding_family g) (fun _ => E → loop F) := ⟨to_fun⟩

variable (γ : smooth_surrounding_family g) (x : E)

def centering_density (γ : smooth_surrounding_family g) : E → ℝ → ℝ := by sorry

lemma strict_mono_integral_centering_density :
  StrictMono (fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s) := sorry

lemma surjective_integral_centering_density :
  Surjective (fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s) := sorry

def reparametrize : E → equivariant_equiv := fun x =>
  let f := fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s
  let iso := StrictMono.orderIsoOfSurjective f
    (γ.strict_mono_integral_centering_density x) (γ.surjective_integral_centering_density x)
  ({ toEquiv := iso.toEquiv
     map_zero' := intervalIntegral.integral_same
     eqv' := fun t => sorry } : equivariant_equiv).symm

@[simp] lemma reparametrize_average :
  ((γ x).reparam (γ.reparametrize x)).average = g x := sorry

end smooth_surrounding_family
