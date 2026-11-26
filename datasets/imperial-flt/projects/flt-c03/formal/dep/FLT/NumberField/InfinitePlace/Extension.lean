module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

@[expose] public section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

/--
If `L/K` and `f : K →+* ℂ`, `g : L →+* ℂ`, then we say `g` is an extension of `f` if
`g` restricted to `K` is `f`.

This is the complex embedding analogue of `InfinitePlace.Extension`.
-/
abbrev IsExtension := g.comp (algebraMap K L) = f

/--
If `L/K` and `f : K →+* ℂ`, `g : L →+* ℂ`, then `g` is a _mixed extension_ of `f` if the
image of `f` is real while the image of `g` is complex.

This is the complex embedding analogue of `InfinitePlace.RamifiedExtension`.
-/
abbrev IsMixedExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g

namespace IsMixedExtension

end IsMixedExtension

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]

variable (L) in
/--
If `L / K` are fields and `v` is an infinite place of `K`, then we say an infinite place `w`
of `L` _extends_ `v` if `w` can be constructed from a complex embedding `L →+* ℂ` whose
restriction to `K` is an associated complex embedding `K →+* ℂ` of `v`.
-/
abbrev Extension (v : InfinitePlace K) := { w : InfinitePlace L // w.comap (algebraMap K L) = v }

namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)

variable (L)

variable (v : InfinitePlace K) (w : v.Extension L)

end Extension

variable (L)

/-- For a given infinite place `v` of `K`, `RamifiedExtension L v` are all the infinite places
of `L / K` that extend `v` and are ramified over `K`. -/
abbrev RamifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }

/-- For a given infinite place `v` of `K`, `UnramifiedExtension L v` are all the infinite places
of `L / K` that extend `v` and are unramified over `K`. -/
abbrev UnramifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }

variable {L v}

namespace RamifiedExtension

theorem comap_eq (w : v.RamifiedExtension L) : w.1.comap (algebraMap K L) = v := sorry

instance : Coe (v.RamifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.2.1⟩

end RamifiedExtension

namespace UnramifiedExtension

theorem comap_eq (w : UnramifiedExtension L v) : w.1.comap (algebraMap K L) = v := sorry

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

end UnramifiedExtension

end NumberField.InfinitePlace
