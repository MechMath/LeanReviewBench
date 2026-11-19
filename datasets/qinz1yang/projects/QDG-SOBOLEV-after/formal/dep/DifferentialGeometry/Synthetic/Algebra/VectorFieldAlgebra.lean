import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel



set_option autoImplicit false






structure DerivationEmbedding (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] where
  embed : V →ₗ[R] Derivation k R R
  embed_injective : Function.Injective embed
  bracket_closed : ∀ X Y : V, ∃ Z : V, embed Z = ⁅embed X, embed Y⁆


structure TimeDerivativeData (R : Type*) (A : Type*) (Time : Type*)
    [CommRing R] [CommRing A] [Algebra R A] where
  
  dt : Derivation R A A
  
  lift : (Time → R) → A
  
  eval : A → Time → R
  
  lift_algebraMap : ∀ (c : R), lift (fun _ => c) = algebraMap R A c
  
  eval_add : ∀ (a b : A) (t : Time), eval (a + b) t = eval a t + eval b t
  
  eval_mul : ∀ (a b : A) (t : Time), eval (a * b) t = eval a t * eval b t
  
  eval_algebraMap : ∀ (c : R) (t : Time), eval (algebraMap R A c) t = c


class TimeRegularFam {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (td : TimeDerivativeData R A Time) where
  
  isSmoothFam : (Time → R) → Prop
  
  eval_lift : ∀ (f : Time → R), isSmoothFam f → ∀ (t : Time),
    td.eval (td.lift f) t = f t
  
  lift_add : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    td.lift (f + g) = td.lift f + td.lift g
  
  lift_mul : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    td.lift (f * g) = td.lift f * td.lift g
  
  isSmoothFam_const : ∀ (c : R), isSmoothFam (fun _ => c)
  
  isSmoothFam_add : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    isSmoothFam (f + g)
  
  isSmoothFam_mul : ∀ (f g : Time → R), isSmoothFam f → isSmoothFam g →
    isSmoothFam (f * g)
  
  isSmoothFam_neg : ∀ (f : Time → R), isSmoothFam f → isSmoothFam (-f)






namespace TimeDerivativeData

variable {R A Time : Type*} [CommRing R] [CommRing A] [Algebra R A]


abbrev isSmoothFam (td : TimeDerivativeData R A Time) [TimeRegularFam td] :
    (Time → R) → Prop :=
  TimeRegularFam.isSmoothFam (td := td)


theorem eval_lift (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time → R) (hf : td.isSmoothFam f) (t : Time) :
    td.eval (td.lift f) t = f t  := by sorry

theorem lift_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f + g) = td.lift f + td.lift g  := by sorry

theorem lift_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f * g) = td.lift f * td.lift g  := by sorry

theorem isSmoothFam_const (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (c : R) : td.isSmoothFam (fun _ => c)  := by sorry

theorem isSmoothFam_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f + g)  := by sorry

theorem isSmoothFam_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f * g)  := by sorry

theorem isSmoothFam_neg (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time → R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (-f)  := by sorry

end TimeDerivativeData





section DerivationEmbeddingDefs

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


def action (emb : DerivationEmbedding k R V) (X : V) (f : R) : R :=
  (emb.embed X) f


noncomputable def bracket (emb : DerivationEmbedding k R V) (X Y : V) : V :=
  Classical.choose (emb.bracket_closed X Y)


theorem bracket_spec (emb : DerivationEmbedding k R V) (X Y : V) :
    emb.embed (bracket emb X Y) = ⁅emb.embed X, emb.embed Y⁆  := by sorry

end DerivationEmbeddingDefs





section CommutatorEndo

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]


def commutatorEndo
    (D_R : R → R) (D_V : V → V)
    (h_add : ∀ v w : V, D_V (v + w) = D_V v + D_V w)
    (h_leibniz : ∀ (f : R) (v : V), D_V (f • v) = D_R f • v + f • D_V v)
    (L : V →ₗ[R] V) : V →ₗ[R] V where
  toFun v := D_V (L v) - L (D_V v)
  map_add' v w := by simp only [map_add, h_add]; abel
  map_smul' c v := by
    simp only [RingHom.id_apply, map_smul, h_leibniz, map_add, map_smul]
    simp only [smul_sub]; abel

end CommutatorEndo





section ActionTheorems

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable (emb : DerivationEmbedding k R V)

theorem action_add_left (X Y : V) (f : R) :
    action emb (X + Y) f = action emb X f + action emb Y f  := by sorry

theorem action_smul_left (c : R) (X : V) (f : R) :
    action emb (c • X) f = c * action emb X f  := by sorry

theorem action_add_right (X : V) (f g : R) :
    action emb X (f + g) = action emb X f + action emb X g  := by sorry

theorem action_smul_right (X : V) (c f : R) :
    action emb X (c * f) = action emb X c * f + c * action emb X f  := by sorry

theorem action_algebraMap (X : V) (c : k) :
    action emb X (algebraMap k R c) = 0  := by sorry

theorem action_one (X : V) : action emb X (1 : R) = 0  := by sorry

theorem action_zero_left (f : R) : action emb (0 : V) f = 0  := by sorry

theorem action_zero_right (X : V) : action emb X (0 : R) = 0  := by sorry

theorem action_neg_right (X : V) (f : R) :
    action emb X (-f) = -action emb X f  := by sorry

theorem action_sub_right (X : V) (f g : R) :
    action emb X (f - g) = action emb X f - action emb X g  := by sorry

theorem action_neg_left (X : V) (f : R) :
    action emb (-X) f = -action emb X f  := by sorry

theorem action_sub_left (X Y : V) (f : R) :
    action emb (X - Y) f = action emb X f - action emb Y f  := by sorry

theorem action_mul_algebraMap (X : V) (c : k) (f : R) :
    action emb X (algebraMap k R c * f) = algebraMap k R c * action emb X f  := by sorry

theorem eq_of_action_eq (X Y : V)
    (h : ∀ f : R, action emb X f = action emb Y f) : X = Y  := by sorry

end ActionTheorems





section BracketTheorems

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable (emb : DerivationEmbedding k R V)


theorem action_bracket (X Y : V) (f : R) :
    action emb (bracket emb X Y) f =
    action emb X (action emb Y f) - action emb Y (action emb X f)  := by sorry

theorem bracket_antisymm (X Y : V) :
    bracket emb X Y = -bracket emb Y X  := by sorry

theorem bracket_add_left (X Y Z : V) :
    bracket emb (X + Y) Z = bracket emb X Z + bracket emb Y Z  := by sorry

theorem bracket_add_right (X Y Z : V) :
    bracket emb X (Y + Z) = bracket emb X Y + bracket emb X Z  := by sorry

theorem bracket_smul_left (c : R) (X Y : V) :
    bracket emb (c • X) Y = c • bracket emb X Y - action emb Y c • X  := by sorry

theorem bracket_smul_right (c : R) (X Y : V) :
    bracket emb X (c • Y) = c • bracket emb X Y + action emb X c • Y  := by sorry

theorem jacobi_identity (X Y Z : V) :
    bracket emb X (bracket emb Y Z) +
    bracket emb Y (bracket emb Z X) +
    bracket emb Z (bracket emb X Y) = 0  := by sorry

theorem bracket_self (X : V) : bracket emb X X = 0  := by sorry

theorem bracket_zero_left (X : V) : bracket emb 0 X = 0  := by sorry

theorem bracket_zero_right (X : V) : bracket emb X 0 = 0  := by sorry

theorem bracket_neg_left (X Y : V) :
    bracket emb (-X) Y = -bracket emb X Y  := by sorry

theorem bracket_neg_right (X Y : V) :
    bracket emb X (-Y) = -bracket emb X Y  := by sorry

end BracketTheorems





section TimeDerivativeTheorems

variable {R : Type*} {A : Type*} {Time : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (td : TimeDerivativeData R A Time)

theorem dt_add (f g : A) : td.dt (f + g) = td.dt f + td.dt g  := by sorry

theorem dt_mul (f g : A) :
    td.dt (f * g) = f • td.dt g + g • td.dt f  := by sorry

theorem t_const_R (c : R) : td.dt (algebraMap R A c) = 0  := by sorry

theorem time_algebraMap_apply {Time' : Type*} (c : R) (t : Time') :
    algebraMap R (Time' → R) c t = c  := by sorry

theorem dt_sub (f g : A) : td.dt (f - g) = td.dt f - td.dt g  := by sorry

theorem dt_neg (f : A) : td.dt (-f) = -td.dt f  := by sorry

theorem dt_zero : td.dt 0 = 0  := by sorry

theorem dt_smul_const (c : R) (f : A) :
    td.dt (algebraMap R A c * f) = algebraMap R A c • td.dt f  := by sorry

end TimeDerivativeTheorems





section DtApply

variable {R : Type*} {A : Type*} {Time : Type*} [CommRing R] [CommRing A] [Algebra R A]


def TimeDerivativeData.dt_apply (td : TimeDerivativeData R A Time)
    (f : Time → R) (t : Time) : R :=
  td.eval (td.dt (td.lift f)) t

theorem TimeDerivativeData.eval_zero (td : TimeDerivativeData R A Time) (t : Time) :
    td.eval 0 t = 0  := by sorry

theorem TimeDerivativeData.isSmoothFam_sub (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f - g)  := by sorry

theorem TimeDerivativeData.isSmoothFam_sum (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι → Time → R)
    (h : ∀ i ∈ s, td.isSmoothFam (f i)) :
    td.isSmoothFam (∑ i ∈ s, f i)  := by sorry

theorem TimeDerivativeData.isSmoothFam_const_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (c : R) (f : Time → R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (fun s => c * f s)  := by sorry

theorem TimeDerivativeData.dt_apply_add (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f + g) t = td.dt_apply f t + td.dt_apply g t  := by sorry

theorem TimeDerivativeData.dt_apply_const (td : TimeDerivativeData R A Time)
    (c : R) (t : Time) :
    td.dt_apply (fun _ => c) t = 0  := by sorry

theorem TimeDerivativeData.dt_apply_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f * g) t = f t * td.dt_apply g t + g t * td.dt_apply f t  := by sorry

theorem TimeDerivativeData.dt_apply_const_mul (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (c : R) (f : Time → R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (fun s => c * f s) t = c * td.dt_apply f t  := by sorry

theorem TimeDerivativeData.dt_apply_neg (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f : Time → R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (-f) t = -td.dt_apply f t  := by sorry

theorem TimeDerivativeData.dt_apply_sub (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    (f g : Time → R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f - g) t = td.dt_apply f t - td.dt_apply g t  := by sorry

theorem TimeDerivativeData.dt_apply_sum (td : TimeDerivativeData R A Time)
    [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι → Time → R) (t : Time)
    (hfs : ∀ i ∈ s, td.isSmoothFam (f i)) :
    td.dt_apply (∑ i ∈ s, f i) t = ∑ i ∈ s, td.dt_apply (f i) t  := by sorry

end DtApply






instance piDFunLike (R Time : Type*) : DFunLike (Time → R) Time (fun _ => R) where
  coe f := f
  coe_injective := fun _ _ h => h


def SpatialTemporalComm {k R V : Type*} {A Time : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time)
    [TimeRegularFam td] : Prop :=
  ∀ (X : V) (f : Time → R) (t : Time), td.isSmoothFam f →
    td.dt_apply (fun s => (emb.embed X) (f s)) t = (emb.embed X) (td.dt_apply f t)






class TimeRegularFam2 {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] where
  
  isSmoothFam2 : (Time × Time → R) → Prop
  
  isSmoothFam2_const : ∀ c, isSmoothFam2 (fun _ => c)
  
  isSmoothFam2_add : ∀ f g, isSmoothFam2 f → isSmoothFam2 g → isSmoothFam2 (f + g)
  
  isSmoothFam2_mul : ∀ f g, isSmoothFam2 f → isSmoothFam2 g → isSmoothFam2 (f * g)
  
  isSmoothFam2_neg : ∀ f, isSmoothFam2 f → isSmoothFam2 (-f)
  
  isSmoothFam2_of_single_fst : ∀ f, td.isSmoothFam f → isSmoothFam2 (fun p => f p.1)
  
  isSmoothFam2_of_single_snd : ∀ f, td.isSmoothFam f → isSmoothFam2 (fun p => f p.2)
  
  diag_isSmoothFam : ∀ G, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ, τ))
  
  slice_left_isSmoothFam : ∀ G τ₀, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ, τ₀))
  
  slice_right_isSmoothFam : ∀ G τ₀, isSmoothFam2 G → td.isSmoothFam (fun τ => G (τ₀, τ))
  
  dt_apply_diag_leibniz : ∀ G (t : Time), isSmoothFam2 G →
      td.dt_apply (fun τ => G (τ, τ)) t =
      td.dt_apply (fun τ => G (τ, t)) t + td.dt_apply (fun τ => G (t, τ)) t


theorem TimeRegularFam2.isSmoothFam2_sub
    {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    {td : TimeDerivativeData R A Time} [TimeRegularFam td] [TimeRegularFam2 td]
    (f g : Time × Time → R)
    (hf : TimeRegularFam2.isSmoothFam2 (td := td) f)
    (hg : TimeRegularFam2.isSmoothFam2 (td := td) g) :
    TimeRegularFam2.isSmoothFam2 (td := td) (f - g)  := by sorry

