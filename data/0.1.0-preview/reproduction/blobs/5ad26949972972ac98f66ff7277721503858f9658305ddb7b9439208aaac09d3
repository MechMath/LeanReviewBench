import dep.Common
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff Topology
structure equivariant_equiv extends Equiv ℝ ℝ where
  map_zero' : toFun 0 = 0
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1
instance : CoeFun equivariant_equiv (fun _ => ℝ → ℝ) := ⟨fun e => e.toFun⟩
namespace equivariant_equiv
@[simp] lemma map_zero (e : equivariant_equiv) : e 0 = 0 := e.map_zero'
@[simp] lemma map_one (e : equivariant_equiv) : e 1 = 1 := by
  simpa using e.eqv' 0
def symm (e : equivariant_equiv) : equivariant_equiv where
  toEquiv := e.toEquiv.symm
  map_zero' := by sorry
  eqv' t := by
    apply e.toEquiv.injective
    change e.toFun (e.toEquiv.symm (t + 1)) = e.toFun (e.toEquiv.symm t + 1)
    rw [e.eqv']
    exact (e.toEquiv.apply_symm_apply (t + 1)).trans
      (congrArg (fun z => z + 1) (e.toEquiv.apply_symm_apply t)).symm
@[simp] lemma symm_apply_apply (e : equivariant_equiv) (x : ℝ) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
@[simp] lemma apply_symm_apply (e : equivariant_equiv) (x : ℝ) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x
end equivariant_equiv
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
def loop.reparam (γ : loop F) (φ : equivariant_equiv) : loop F where
  to_fun := γ ∘ φ
  per' t := by change γ (φ (t + 1)) = γ (φ t); rw [φ.eqv', γ.per']
structure smooth_surrounding_family (g : E → F) where
  to_fun : E → loop F
  smooth : ∀ x s, smooth_at (fun p : E × ℝ => to_fun p.1 p.2) (x, s)
  surrounds : ∀ x, (to_fun x).surrounds (g x)
namespace smooth_surrounding_family
variable {g : E → F}
instance : CoeFun (smooth_surrounding_family g) (fun _ => E → loop F) := ⟨to_fun⟩
variable (γ : smooth_surrounding_family g) (x : E)
protected lemma continuous : Continuous (γ x) := by sorry
def centering_density (γ : smooth_surrounding_family g) : E → ℝ → ℝ := by sorry
lemma centering_density_pos (t : ℝ) : 0 < γ.centering_density x t := by sorry
@[simp] lemma integral_centering_density_eq_one (t : ℝ) :
  ∫ s in t..(t+1), γ.centering_density x s = 1 := by sorry
lemma centering_density_smooth (t : ℝ) :
  smooth_at (fun p : E × ℝ => γ.centering_density p.1 p.2) (x, t) := by sorry
lemma centering_density_continuous (t : ℝ) :
  ContinuousAt (γ.centering_density x) t := by sorry
lemma centering_density_interval_integrable (a b : ℝ) :
  IntervalIntegrable (γ.centering_density x) volume a b := by sorry
@[simp] lemma average_centering_density :
  ∫ s in (0 : ℝ)..1, (γ.centering_density x s) • (γ x s) = g x := by sorry
lemma strict_mono_integral_centering_density :
  StrictMono (fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s) := by sorry
lemma surjective_integral_centering_density :
  Surjective (fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s) := by sorry
def reparametrize : E → equivariant_equiv := fun x =>
  let f := fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s
  let iso := StrictMono.orderIsoOfSurjective f
    (γ.strict_mono_integral_centering_density x) (γ.surjective_integral_centering_density x)
  ({ toEquiv := iso.toEquiv
     map_zero' := intervalIntegral.integral_same
     eqv' := fun t => by
       change (∫ s in (0 : ℝ)..(t+1), γ.centering_density x s) =
         (∫ s in (0 : ℝ)..t, γ.centering_density x s) + 1
       have h₁ := γ.centering_density_interval_integrable x 0 t
       have h₂ := γ.centering_density_interval_integrable x t (t + 1)
       rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
       simp } : equivariant_equiv).symm
lemma coe_reparametrize_symm :
  ((γ.reparametrize x).symm : ℝ → ℝ) = fun t => ∫ s in (0 : ℝ)..t, γ.centering_density x s := rfl
@[simp] lemma reparametrize_map_zero : γ.reparametrize x 0 = 0 := equivariant_equiv.map_zero _
@[simp] lemma reparametrize_map_one : γ.reparametrize x 1 = 1 := equivariant_equiv.map_one _
lemma has_deriv_at_reparametrize_symm (s : ℝ) :
  HasDerivAt (γ.reparametrize x).symm (γ.centering_density x s) s := by
  simp only [coe_reparametrize_symm]
  apply intervalIntegral.integral_hasDerivAt_right
    (γ.centering_density_interval_integrable x 0 s) _ (γ.centering_density_continuous x s)
  sorry
lemma reparametrize_smooth_at (s : ℝ) :
  smooth_at (fun p : E × ℝ => γ.reparametrize p.1 p.2) (x, s) := by sorry
lemma reparametrize_continuous : Continuous (γ.reparametrize x : ℝ → ℝ) := by sorry
@[simp] lemma reparametrize_average :
  ((γ x).reparam (γ.reparametrize x)).average = g x := by
  change ∫ s in (0 : ℝ)..1, γ x (γ.reparametrize x s) = g x
  have h₁ : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (γ.reparametrize x).symm (γ.centering_density x s) s :=
    fun s _ => γ.has_deriv_at_reparametrize_symm x s
  have h₂ : ContinuousOn (fun s => γ.centering_density x s) (Set.uIcc (0 : ℝ) 1) :=
    fun s _ => (γ.centering_density_continuous x s).continuousWithinAt
  have h₃ : Continuous (fun s => γ x (γ.reparametrize x s)) :=
    (γ.continuous x).comp (γ.reparametrize_continuous x)
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one,
    ← intervalIntegral.integral_deriv_smul_comp h₁ h₂ h₃]
  simpa only [Function.comp_apply, equivariant_equiv.apply_symm_apply] using
    γ.average_centering_density x
end smooth_surrounding_family
