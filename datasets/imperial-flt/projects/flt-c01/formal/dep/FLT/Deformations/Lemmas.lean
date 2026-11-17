module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-- The continuous group homomorphism on units induced by a `ContinuousMonoidHom`. -/
@[simps!]
def Units.mapₜ {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f,
  continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.2.comp Units.continuous_val,
    MulOpposite.continuous_op.comp (f.2.comp Units.continuous_coe_inv)⟩)⟩

/-- The `ContinuousAlgHom` between spaces of square matrices induced by an `ContinuousAlgHom`
between their coefficients. This is Matrix.map as an `ContinuousAlgHom`. -/
@[simps!]
def ContinuousAlgHom.mapMatrix
    {R A B n : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B)
    [Fintype n] [DecidableEq n] :
    Matrix n n A →A[R] Matrix n n B :=
  ⟨f.1.mapMatrix, Continuous.matrix_map continuous_id' f.2⟩

/-- Coerce a `ContinuousAlgHom` to `ContinuousMonoidHom`. -/
def ContinuousAlgHom.toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) : A →ₜ* B :=
  ⟨f.1.toMonoidHom, f.2⟩

instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G] :
    MulAction α (M →* G) where
  smul a f := ⟨⟨a • f, sorry⟩, sorry⟩
  one_smul _ := sorry
  mul_smul a b f := sorry

instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G] :
    MulAction α (M →ₜ* G) where
  smul a f := ⟨a • f, .const_smul f.2 _⟩
  one_smul _ := sorry
  mul_smul a b f := sorry

instance {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G := sorry

@[to_additive]
instance IsTopologicalGroup.discreteUniformity
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    letI := IsTopologicalGroup.rightUniformSpace G
    DiscreteUniformity G := sorry

nonrec
instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A] :
    IsLocalHom (ContinuousAlgHom.id R A) := sorry

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := sorry

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃A[R] B) : IsLocalHom (f : A →A[R] B) := sorry

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := sorry

instance {A B : Type*} [Semiring A] [Semiring B]
    (F : Type*) [EquivLike F A B] [RingEquivClass F A B] (f : F) :
    IsLocalHom (RingHomClass.toRingHom f) := sorry

instance {R S} [Semiring R] [Semiring S] (e : R ≃+* S) : IsLocalHom e.toRingHom := sorry

instance ContinuousAlgHom.isLocalHom_comp {R A B C : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B →A[R] C} {f : A →A[R] B}
    [IsLocalHom g] [IsLocalHom f] :
    IsLocalHom (g.comp f) := sorry

instance {R : Type*} [CommSemiring R] : IsLocalHom (algebraMap R R) := sorry

open IsLocalRing in
instance {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (ResidueField R)) := sorry

/-- Given a field extension, this is an arbitrarily chosen map between their `AlgebraicClosure`s. -/
noncomputable
def AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

/-- Given a `ContinuousMonoidHom` from a group to a monoid, we may lift it to map into the group
of units of the monoid. -/
@[simps!]
def ContinuousMonoidHom.toHomUnits {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace M] (f : G →ₜ* M) : G →ₜ* Mˣ :=
  ⟨MonoidHom.toHomUnits f, continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.continuous, sorry⟩)⟩

/-- `Units.val` as a `ContinuousMonoidHom`. -/
@[simps!]
def Units.coeHomₜ (M : Type*) [Monoid M] [TopologicalSpace M] : Mˣ →ₜ* M :=
  ⟨coeHom M, Units.continuous_val⟩

instance {A n m : Type*} [CommRing A] [TopologicalSpace A]
    [Finite n] [Finite m] [IsTopologicalRing A] :
    IsModuleTopology A (Matrix n m A) := sorry

/-- We can upgrade an `AlgEquiv` between algebras with the module topology
into a `ContinuousAlgEquiv`. -/
def ContinuousAlgEquiv.ofIsModuleTopology {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace R] [IsModuleTopology R A] [IsModuleTopology R B] (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd R B
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd R A
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

instance {G K L : Type*} [Field K] [Field L] [Algebra K L] [Monoid G] [MulSemiringAction G L]
    [SMulCommClass G K L]
    (E : IntermediateField K L) [Normal K E] : MulSemiringAction G E where
  smul σ x := ⟨σ • x, sorry⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

open NumberField in
instance {G K : Type*} [Field K] [Monoid G] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) where
  smul σ x := ⟨σ • x, x.2.map (MulSemiringAction.toAlgHom ℤ K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (R : ValuationSubring K)
    [FaithfulSMul K A] : FaithfulSMul R A := sorry

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E := sorry

instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := sorry
  smul_def' _ _ := sorry

instance IntermediateField.smulCommClass_of_normal
    {K L G : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] [Normal K E] :
    SMulCommClass G K E := sorry

instance ValuationSubring.smulCommClass
    (K L G : Type*) [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L]
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G O L := sorry

instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := sorry

noncomputable
instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul
