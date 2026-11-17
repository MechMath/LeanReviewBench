module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d : ℕ}

/-- Variables of a local expansion: `none` is `T`, `some none` is the auxiliary slot, and
`some (some j)` is the visible jet `Y_(j+1)`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and the visible jets `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared auxiliary slot. -/
def localAux (d : ℕ) : LocalVariable d := some none

/-- The auxiliary slot after the rewrite, where it holds the hidden error. -/
abbrev localE (d : ℕ) : LocalVariable d := localAux d

/-- The local variable for the visible jet `Y_(j+1)`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible jets have weight zero. -/
def localContactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

end ReedSolomon.HiddenDerivative
