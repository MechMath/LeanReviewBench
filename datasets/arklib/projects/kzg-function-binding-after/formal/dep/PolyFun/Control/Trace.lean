module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas

@[expose] public section

universe u u' u'' v

namespace Control

/--
`Trace ω X` is the type `X → ω` of stateless valuations from inputs `X` into
a monoid `ω`.  It inherits a monoid structure from `Pi.monoid`, with `1`
the constant trace and `*` the pointwise product.

See the module docstring for motivation and the catalogue of instances
(`QueryLog`, `QueryCount`, ...) it is intended to subsume.
-/
abbrev Trace (ω : Type u) (X : Type v) : Type max u v := X → ω

namespace Trace

variable {ω : Type u} {ω' : Type u'} {ω'' : Type u''} {X Y Z : Type v}

/-- Post-compose a trace with a monoid homomorphism. -/
def map [MulOneClass ω] [MulOneClass ω'] (φ : ω →* ω') (t : Trace ω X) :
    Trace ω' X := φ ∘ t

end Trace

end Control
