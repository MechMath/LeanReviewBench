module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Data.Finsupp.Fin

@[expose] public section

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} {M : Type*} [Zero M]

/-- `init` for maps `Fin n →₀ M`. See `Fin.init` for more details. -/
def init (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.init s)

/-- `snoc` for maps `Fin n →₀ M`. See `Fin.snoc` for more details. -/
def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc s y : Fin (n + 1) → M)

/-- `insertNth` for maps `Fin n →₀ M`. See `Fin.insertNth` for more details. -/
def insertNth (p : Fin (n + 1)) (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.insertNth p y s : Fin (n + 1) → M)

section Remove

variable (p : Fin (n + 1)) (s : Fin (n + 1) →₀ M) (y : M) (i : Fin n)

end Remove

section Add

variable (p : Fin (n + 1)) (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M) (i : Fin n)

variable {y} {s}

end Add

section BigOperators

variable {M N : Type*}

end BigOperators

end Finsupp
