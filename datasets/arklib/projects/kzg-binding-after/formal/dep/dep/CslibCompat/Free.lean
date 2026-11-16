module
public import Cslib.Foundations.Data.PFunctor.Free
@[expose] public section
namespace PFunctor.FreeM
universe u uB v w z
variable {P : PFunctor.{u, uB}} {α : Type v} {β : Type w} {γ : Type z}
@[simp]
theorem map_pure (f : α → β) (x : α) : map f (pure x : P.FreeM α) = pure (f x) := rfl
@[simp]
theorem map_bind (f : β → γ) (x : P.FreeM α) (cont : α → P.FreeM β) :
    map f (x.bind cont) = x.bind fun a => (cont a).map f := by
  simp_rw [← bind_pure_comp, FreeM.bind_assoc]
@[simp]
theorem liftM_lift_eq_self {α : Type uB} (x : P.FreeM α) : FreeM.liftM FreeM.lift x = x := by
  induction x with
  | pure _ => rfl
  | lift_bind _ _ ih => simp [ih]
theorem liftM_comp {m : Type uB → Type v} [Monad m] [LawfulMonad m]
    {Q : PFunctor.{u, uB}} {α : Type uB} (x : P.FreeM α)
    (first : (a : P.A) → Q.FreeM (P.B a)) (second : (a : Q.A) → m (Q.B a)) :
    (x.liftM first).liftM second = x.liftM fun a => (first a).liftM second :=
  (isMonadHom_liftM second).map_pfunctorFreeMLiftM first x
end PFunctor.FreeM
