module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

open IsDedekindDomain HeightOneSpectrum adicCompletion NumberField UniformSpace.Completion

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]

instance : Infinite R := sorry

namespace Rat.HeightOneSpectrum.IsIntegralClosure

instance : Module.Free ℤ R := sorry

instance : Module.Finite ℤ R := sorry

instance : IsPrincipalIdealRing R := sorry

end IsIntegralClosure

variable [IsDedekindDomain R]

variable [IsFractionRing R ℚ]

end Rat.HeightOneSpectrum
