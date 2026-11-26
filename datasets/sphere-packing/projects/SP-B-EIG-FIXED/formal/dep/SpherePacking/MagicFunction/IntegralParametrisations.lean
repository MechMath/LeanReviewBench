module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

open Set Complex Real

local notation "V" => EuclideanSpace ℝ (Fin 8)

local notation "ℍ₀" => UpperHalfPlane.upperHalfPlaneSet

namespace MagicFunction.Parametrisations

noncomputable section Parametrisations

def z₁ (t : Icc (0 : ℝ) 1) : ℂ := -1 + I * t

def z₁' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₁ t

def z₂ (t : Icc (0 : ℝ) 1) : ℂ := -1 + t + I

def z₂' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₂ t

def z₃ (t : Icc (0 : ℝ) 1) : ℂ := 1 + I * t

def z₃' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₃ t

def z₄ (t : Icc (0 : ℝ) 1) : ℂ := 1 - t + I

def z₄' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₄ t

def z₅ (t : Icc (0 : ℝ) 1) : ℂ := I * t

def z₅' (t : ℝ) : ℂ := IccExtend (zero_le_one) z₅ t

def z₆ (t : Ici (1 : ℝ)) : ℂ := I * t

def z₆' (t : ℝ) : ℂ := IciExtend z₆ t

end Parametrisations

section UpperHalfPlane

open scoped UpperHalfPlane

end UpperHalfPlane

section eq_of_mem

end eq_of_mem

section transforms_mem

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup

open scoped MatrixGroups ComplexConjugate

end transforms_mem

end MagicFunction.Parametrisations
