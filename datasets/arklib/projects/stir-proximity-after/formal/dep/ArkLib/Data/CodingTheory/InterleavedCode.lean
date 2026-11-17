module

public import Batteries.Data.Fin.Fold
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Qify
public import Mathlib.Topology.MetricSpace.Infsep
public import dep.ArkLib.Data.CodingTheory.Basic.Distance
public import dep.ArkLib.Data.CodingTheory.Basic.LinearCode
public import dep.ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

section InterleavedCodeDefinitions

variable (F : Type*) [Semiring F]

variable (A : Type*) [AddCommMonoid A] [Module F A]

variable (κ ι : Type*) [Fintype κ] [Fintype ι]

variable (MC : ModuleCode ι F A)

variable (C : Set (ι → A))

open NNReal

namespace Code

/-- A word is a vector (ι → A) -/
@[simp]
abbrev Word := ι → A

@[simp]
abbrev InterleavedSymbol := κ → A

/-- A word stack is a (row-wise) matrix (κ → ι → A) where each ROW is a word -/
@[simp]
abbrev WordStack := Matrix κ ι A

@[simp]
def WordStack.getRowWord {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (k : κ) : Word A ι := u k

@[simp]
def WordStack.getSymbol {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (i : ι) : InterleavedSymbol A κ := u.transpose i

/-- An interleaved word is a (column-wise) matrix (ι → (κ → A)) where each ROW is a word, each
  column i is a symbol (κ → A) for the interleaved code MC^⋈ κ. -/
@[simp]
abbrev InterleavedWord := Matrix ι κ A

@[simp]
def InterleavedWord.getRowWord {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (k : κ) : Word A ι := v.transpose k

@[simp]
def InterleavedWord.getSymbol {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (i : ι) : InterleavedSymbol A κ := v i

/-- The set of interleaved words where each row belongs to a code C.
    This is a generic version that works for any code represented as a Set. -/
@[simp]
def interleavedCodeSet {A : Type*} {κ ι : Type*}
    (C : Set (ι → A)) : Set (Matrix ι κ A) :=
  { V : Matrix ι κ A | ∀ k : κ, V.transpose k ∈ C }

/-- If C is finite and membership is decidable, then interleavedCodeSet C is finite. -/
@[simp]
noncomputable instance interleavedCodeSet_fintype {A : Type*} {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) :
    Fintype (interleavedCodeSet (κ := κ) (ι := ι) C) := by
  exact Fintype.ofFinite (interleavedCodeSet C)

/-- Interleaved code submodule of any `ModuleCode`, where each row belongs to the code. -/
@[simp]
def ModuleCode.moduleInterleavedCode : ModuleCode ι F (InterleavedSymbol A κ) := {
  -- Simple condition wrapping over Matrix
  carrier := interleavedCodeSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

@[simp]
def codewordStackSet {A : Type*} {κ ι : Type*} (C : Set (ι → A)) : Set (WordStack A κ ι) :=
  { V : WordStack A κ ι | ∀ k, V.getRowWord k ∈ C }

@[simp]
def ModuleCode.codewordStackSubmodule : Submodule F (WordStack A κ ι) := {
  -- Simple condition wrapping over Matrix
  carrier := codewordStackSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

instance instMembershipWordStackCodewordStackSet : Membership (α := WordStack A κ ι)
  (γ := codewordStackSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

instance instMembershipInterleavedWordInterleavedCodeSet :
  Membership (InterleavedWord A κ ι) (interleavedCodeSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

/-- An interleaved codeword is a (column-wise) matrix (ι → (κ → A)) where each ROW is a codeword
  of the base module code MC. -/
@[simp]
abbrev InterleavedCodeword := interleavedCodeSet (κ := κ) (C := C)

/-- A codeword stack is a (row-wise) matrix (κ → ι → A) where each ROW is a codeword of MC. -/
@[simp]
abbrev CodewordStack := codewordStackSet (κ := κ) (C := C)

@[simp]
def interleaveWordStack {A : Type*} {κ ι : Type*}
    (u : WordStack A κ ι) : InterleavedWord A κ ι := u.transpose

/-- Interleave a codeword stack into an interleaved codeword. -/
@[simp]
def interleaveCodewordStack (u : CodewordStack A κ ι C) : InterleavedCodeword A κ ι C :=
  ⟨interleaveWordStack u.val, sorry
  ⟩

@[simp]
def finMapTwoWords {A : Type*} {ι : Type*}
    (u₀ u₁ : Word A ι) : WordStack A (κ := Fin 2) (ι := ι) := fun rowIdx =>
  match rowIdx with
  | ⟨0, _⟩ => u₀
  | ⟨1, _⟩ => u₁

@[simp]
def finMapTwoCodewords (u₀ u₁ : C) :
    CodewordStack A (κ := Fin 2) (ι := ι) C :=
  ⟨finMapTwoWords u₀ u₁, sorry
  ⟩

/-- Interleave two codewords u₀ and u₁ into a single interleaved codeword -/
@[simp]
def interleaveTwoWords (u₀ u₁ : Word A ι) : InterleavedWord A (Fin 2) ι :=
  interleaveWordStack (κ := Fin 2) (ι := ι) (u := finMapTwoWords u₀ u₁)

@[simp]
def interleaveTwoCodewords (u₀ u₁ : C) : InterleavedCodeword A (κ := Fin 2) ι C :=
  interleaveCodewordStack A (κ := Fin 2) (ι := ι) (u := finMapTwoCodewords A ι C u₀ u₁)

/-- Combine two codeword stacks with different κ types by stacking vertically -/
@[simp]
def finMapCodewordStacksAppend {κ₁ κ₂ : Type*}
    (u : CodewordStack A κ₁ ι C) (v : CodewordStack A κ₂ ι C) :
    CodewordStack A (Sum κ₁ κ₂) ι C :=
  ⟨fun s =>
    match s with
    | Sum.inl k₁ => u.val k₁
    | Sum.inr k₂ => v.val k₂, sorry
  ⟩

/-- Type class for overloading the interleave notation.
Interleaving a word stack -> interleaved word
Interleaving a codeword stack -> interleaved codeword -/
class Interleavable (α : Type*) (β : outParam Type*) where
  interleave : α → β

notation:65 "⋈|" u => Interleavable.interleave u

class Interleavable₂ (α : Type*) (β : outParam Type*) where
  interleave₂ : α → α → β

notation:65 u "⋈₂" v => Interleavable₂.interleave₂ u v

/-- Typeclass for interleaving codes (preserving their structure).
    For Set → Set, for ModuleCode → ModuleCode, etc. -/
class CodeInterleavable.{u, v} (Code : Type*) (InterleavedCode : outParam (Type u → Type v)) where
  interleaveCode : Code → (κ : Type u) → InterleavedCode κ

notation:20 C "^⋈" κ => @CodeInterleavable.interleaveCode _ _ _ C κ

@[simp]
instance : Interleavable (α := WordStack A κ ι) (β := InterleavedWord A κ ι) where
  interleave := interleaveWordStack

@[simp]
instance : Interleavable (α := CodewordStack A κ ι C) (β := InterleavedCodeword A κ ι C) where
  interleave u := ⟨interleaveWordStack u.val, sorry
  ⟩

@[simp]
instance : Interleavable (α := ModuleCode.codewordStackSubmodule F A κ ι (MC := MC))
    (β := ModuleCode.moduleInterleavedCode F A κ ι (MC := MC)) where
  interleave u := interleaveCodewordStack (κ := κ) (ι := ι) (u := u)

@[simp]
instance : Interleavable₂ (α := Word A ι) (β := InterleavedWord A (Fin 2) ι) where
  interleave₂ u₀ u₁ := interleaveTwoWords A ι u₀ u₁

@[simp]
instance : Interleavable₂ (α := C) (β := InterleavedCodeword A (κ := (Fin 2)) ι C) where
  interleave₂ u₀ u₁ := interleaveTwoCodewords A ι C u₀ u₁

/-- Interleave a Set-based code into an interleaved code set. -/
@[simp]
instance : CodeInterleavable (Code := Set (ι → A))
    (InterleavedCode := fun κ => Set (Matrix ι κ A)) where
  interleaveCode C := fun κ => interleavedCodeSet (κ := κ) C

/-- Interleave a ModuleCode into an interleaved ModuleCode (preserving submodule structure). -/
@[simp]
instance : CodeInterleavable (Code := ModuleCode ι F A)
    (InterleavedCode := fun κ => ModuleCode ι F (InterleavedSymbol A κ)) where
  interleaveCode MC := fun κ => ModuleCode.moduleInterleavedCode
    (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)

@[simp]
noncomputable instance instFintypeInterleavedModuleCode [Fintype A] : Fintype (MC ^⋈ κ) := by
  exact Fintype.ofFinite ((MC ^⋈ κ) : Set (ι → (κ → A)))

section Finrank

end Finrank

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (WordStack A κ₁ ι) (WordStack A κ₂ ι) (WordStack A (Sum κ₁ κ₂) ι) where
  hAppend u v := fun s =>
    match s with
    | Sum.inl k₁ => u k₁
    | Sum.inr k₂ => v k₂

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (CodewordStack A κ₁ ι C) (CodewordStack A κ₂ ι C)
      (CodewordStack A (Sum κ₁ κ₂) ι C) where
  hAppend u v := finMapCodewordStacksAppend A ι C (κ₁ := κ₁) (κ₂ := κ₂) u v

namespace InterleavedCode

variable (RowIdx SymbolIdx : Type*)

variable (RowType SymbolType CellTy : Type*)

/-- 1. GetRow -/
class GetRow (α : Type*) (RowIdx RowType : outParam Type*) where
  getRow : (u : α) → (rowIdx : RowIdx) → RowType

/-- 2. GetSymbol -/
class GetSymbol (α : Type*) (SymbolIdx SymbolType : outParam Type*) where
  getSymbol : (u : α) → (symbolIdx : SymbolIdx) → SymbolType

/-- 3. GetCell -/
class GetCell (α : Type*) (RowIdx SymbolIdx : Type*) (CellTy : outParam Type*) where
  getCell : (u : α) → (rowIdx : RowIdx) → (symbolIdx : SymbolIdx) → CellTy

export GetRow (getRow)

export GetSymbol (getSymbol)

export GetCell (getCell)

/-- 6. InterleavedStructure: Extends accessors and defines equality via rows/symbols/cells.
    Applied to the InterleavedElementType. -/
class InterleavedStructure (α : Type*) (RowIdx SymbolIdx : outParam Type*)
    (RowType SymbolType CellTy : outParam Type*)
    extends GetRow α RowIdx RowType,
            GetSymbol α SymbolIdx SymbolType,
            GetCell α RowIdx SymbolIdx CellTy where
  eq_iff_all_rows_eq {u v : α} : u = v ↔ ∀ i, getRow u i = getRow v i
  eq_iff_all_symbols_eq {u v : α} : u = v ↔ ∀ k, getSymbol u k = getSymbol v k
  eq_iff_all_cells_eq {u v : α} : u = v ↔ ∀ i k, getCell u i k = getCell v i k

export InterleavedStructure (eq_iff_all_rows_eq eq_iff_all_symbols_eq eq_iff_all_cells_eq)

@[simp] instance (priority := 500) instInterleavedStructureWordStack :
    InterleavedStructure (α := WordStack A κ ι) (RowIdx := κ) (SymbolIdx := ι)
      (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u k := WordStack.getRowWord u k
  getSymbol u i := WordStack.getSymbol u i
  getCell u k i := (WordStack.getRowWord u k) i
  eq_iff_all_rows_eq := sorry
  eq_iff_all_symbols_eq := sorry
  eq_iff_all_cells_eq := sorry

@[simp] instance instInterleavedStructureCodewordStack :
    InterleavedStructure (α := CodewordStack A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u k := ⟨u.val k, sorry
  ⟩
  getSymbol u i := u.val.transpose i
  getCell u k i := u.val k i
  eq_iff_all_rows_eq := sorry
  eq_iff_all_symbols_eq := sorry
  eq_iff_all_cells_eq := sorry

@[simp] instance instInterleavedStructureInterleavedWord :
    InterleavedStructure (α := InterleavedWord A κ ι) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u i := InterleavedWord.getRowWord u i
  getSymbol u k := InterleavedWord.getSymbol u k
  getCell u i k := (InterleavedWord.getRowWord u i) k
  eq_iff_all_rows_eq := sorry
  eq_iff_all_symbols_eq := sorry
  eq_iff_all_cells_eq := sorry

@[simp] instance instInterleavedStructureInterleavedCodeword :
    InterleavedStructure (α := InterleavedCodeword A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  -- No separate functions cuz InterleavedCodeword is a subtype
  getRow u k := ⟨(Matrix.transpose u) k, sorry
  ⟩
  getSymbol u colIdx := u.val colIdx
  getCell u k i := Matrix.transpose u k i
  eq_iff_all_rows_eq := sorry
  eq_iff_all_symbols_eq := sorry
  eq_iff_all_cells_eq := sorry

class Stackifiable (α : Type*) (β : outParam Type*) where
  stackify : α → β

notation:65 "⋈⁻¹|" u => Stackifiable.stackify u

@[simp]
instance : Stackifiable (α := InterleavedWord A κ ι) (β := WordStack A κ ι) where
  stackify u := u.transpose

@[simp]
instance : Stackifiable (α := InterleavedCodeword A κ ι C) (β := CodewordStack A κ ι C) where
  stackify u := ⟨u.val.transpose, sorry
  ⟩

/-- Notation for stacking one stack on top of another -/
infixl:65 " ++ₕ " => HAppend.hAppend

@[simp]
instance instNonemptyInterleavedCode [Nonempty C] :
    Nonempty (C ^⋈ κ) := sorry

end InterleavedCode

section JointProximityDefinitions

variable {κ ι : Type*} [Fintype ι] [Fintype κ]
  {A : Type*} (C : Set (ι → A)) [DecidableEq A]

/-- The list of `κ`-fold codeword stacks whose interleaved codeword forms are
(less-than)-`δ`-close to `⋈|u`. -/
def relHammingBallInterleavedCode (u : WordStack A κ ι) (δ : ℝ≥0) : Set (CodewordStack A κ ι C) :=
  {v : CodewordStack A κ ι (C := C) | δᵣ(⋈|u, (⋈|v).val) < δ}

/-- `Λᵢ(u, C, δ)` denotes the list of `κ`-fold codeword stacks whose interleaved codeword forms are
(less-than)-`δ`-close to `⋈|u`. -/
notation "Λᵢ(" u "," C "," δ ")" => relHammingBallInterleavedCode C u δ

end JointProximityDefinitions

end Code

end InterleavedCodeDefinitions
