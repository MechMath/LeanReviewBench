module

public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section

open Matrix TransvectionStruct

namespace Matrix

section TransvectionStruct_dot_map

variable {n : Type*} {R S : Type*} [CommRing R] [CommRing S]
    [DecidableEq n] (f : R →+* S)

/-- Base change of a TransvectionStruct along a ring homomorphism. -/
def TransvectionStruct.map {n : Type*} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : TransvectionStruct n R) :
    TransvectionStruct n S where
  i := t.i
  j := t.j
  hij := t.hij
  c := f t.c

end TransvectionStruct_dot_map

open Pivot

variable {n : Type*} {R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

end Matrix
