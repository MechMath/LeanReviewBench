import Lean
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Command
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

abbrev Equation1000.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y y)))

def Law1000 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1001.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y z)))

def Law1001 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1002.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y w)))

def Law1002 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1003.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y u)))

def Law1003 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1004.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z x)))

def Law1004 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1005.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z y)))

def Law1005 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1006.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z z)))

def Law1006 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1007.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z w)))

def Law1007 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1008.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z u)))

def Law1008 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1009.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w x)))

def Law1009 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1010.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w y)))

def Law1010 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1011.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w z)))

def Law1011 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1012.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w w)))

def Law1012 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1013.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w u)))

def Law1013 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1014.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u x)))

def Law1014 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1015.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u y)))

def Law1015 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1016.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u z)))

def Law1016 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1017.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u w)))

def Law1017 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1018.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u u)))

def Law1018 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1019.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u v)))

def Law1019 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))

abbrev Equation1020.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x))

def Law1020 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1021.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y))

def Law1021 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1022.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x))

def Law1022 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1023.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y))

def Law1023 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1024.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z))

def Law1024 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1025.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x))

def Law1025 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1026.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y))

def Law1026 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1027.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z))

def Law1027 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1028.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x))

def Law1028 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1029.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y))

def Law1029 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1030.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z))

def Law1030 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1031.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x))

def Law1031 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1032.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y))

def Law1032 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1033.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z))

def Law1033 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1034.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w))

def Law1034 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1035.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x))

def Law1035 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1036.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y))

def Law1036 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1037.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z))

def Law1037 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1038.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x))

def Law1038 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1039.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y))

def Law1039 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1040.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z))

def Law1040 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1041.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x))

def Law1041 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1042.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y))

def Law1042 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1043.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z))

def Law1043 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1044.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w))

def Law1044 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1045.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x))

def Law1045 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1046.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y))

def Law1046 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1047.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z))

def Law1047 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1048.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x))

def Law1048 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1049.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y))

def Law1049 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1050.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z))

def Law1050 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1051.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x))

def Law1051 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1052.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y))

def Law1052 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1053.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z))

def Law1053 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1054.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w))

def Law1054 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1055.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x))

def Law1055 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1056.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y))

def Law1056 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1057.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z))

def Law1057 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1058.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w))

def Law1058 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1059.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x))

def Law1059 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1060.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y))

def Law1060 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1061.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z))

def Law1061 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1062.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w))

def Law1062 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1063.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x))

def Law1063 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1064.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y))

def Law1064 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1065.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z))

def Law1065 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1066.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w))

def Law1066 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1067.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x))

def Law1067 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1068.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y))

def Law1068 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1069.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z))

def Law1069 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1070.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w))

def Law1070 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1071.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u))

def Law1071 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1072.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x))

def Law1072 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1073.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y))

def Law1073 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1074.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) z))

def Law1074 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1075.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x))

def Law1075 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1076.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y))

def Law1076 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1077.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z))

def Law1077 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1078.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) x))

def Law1078 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1079.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) y))

def Law1079 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1080.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) z))

def Law1080 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1081.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) w))

def Law1081 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1082.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x))

def Law1082 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1083.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y))

def Law1083 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1084.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z))

def Law1084 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1085.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x))

def Law1085 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1086.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y))

def Law1086 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1087.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z))

def Law1087 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1088.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x))

def Law1088 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1089.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y))

def Law1089 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1090.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z))

def Law1090 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1091.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w))

def Law1091 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1092.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) x))

def Law1092 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1093.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) y))

def Law1093 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1094.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) z))

def Law1094 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1095.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) w))

def Law1095 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1096.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) x))

def Law1096 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1097.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) y))

def Law1097 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1098.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) z))

def Law1098 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1099.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) w))

def Law1099 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1100.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) x))

def Law1100 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1101.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) y))

def Law1101 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1102.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) z))

def Law1102 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1103.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) w))

def Law1103 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1104.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) x))

def Law1104 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1105.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) y))

def Law1105 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1106.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) z))

def Law1106 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1107.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) w))

def Law1107 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1108.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) u))

def Law1108 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1109.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x))

def Law1109 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1110.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y))

def Law1110 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1111.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z))

def Law1111 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1112.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x))

def Law1112 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1113.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y))

def Law1113 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1114.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z))

def Law1114 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1115.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x))

def Law1115 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1116.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y))

def Law1116 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1117.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z))

def Law1117 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1118.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w))

def Law1118 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1119.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x))

def Law1119 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1120.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y))

def Law1120 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1121.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z))

def Law1121 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1122.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x))

def Law1122 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1123.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y))

def Law1123 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1124.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z))

def Law1124 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1125.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x))

def Law1125 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1126.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y))

def Law1126 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1127.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z))

def Law1127 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1128.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w))

def Law1128 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1129.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x))

def Law1129 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1130.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y))

def Law1130 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1131.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z))

def Law1131 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1132.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w))

def Law1132 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1133.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x))

def Law1133 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1134.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y))

def Law1134 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1135.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z))

def Law1135 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1136.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w))

def Law1136 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1137.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x))

def Law1137 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1138.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y))

def Law1138 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1139.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z))

def Law1139 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1140.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w))

def Law1140 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1141.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x))

def Law1141 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1142.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y))

def Law1142 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1143.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z))

def Law1143 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1144.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w))

def Law1144 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1145.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u))

def Law1145 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1146.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) x))

def Law1146 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1147.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) y))

def Law1147 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1148.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) z))

def Law1148 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1149.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) w))

def Law1149 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1150.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) x))

def Law1150 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1151.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) y))

def Law1151 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1152.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) z))

def Law1152 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1153.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) w))

def Law1153 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1154.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) x))

def Law1154 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1155.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) y))

def Law1155 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1156.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) z))

def Law1156 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1157.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) w))

def Law1157 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1158.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) x))

def Law1158 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1159.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) y))

def Law1159 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1160.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) z))

def Law1160 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1161.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) w))

def Law1161 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1162.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) u))

def Law1162 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1163.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) x))

def Law1163 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1164.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) y))

def Law1164 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1165.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) z))

def Law1165 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1166.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) w))

def Law1166 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1167.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) x))

def Law1167 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1168.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) y))

def Law1168 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1169.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) z))

def Law1169 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1170.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) w))

def Law1170 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1171.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) x))

def Law1171 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1172.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) y))

def Law1172 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1173.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) z))

def Law1173 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1174.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) w))

def Law1174 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1175.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) x))

def Law1175 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1176.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) y))

def Law1176 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1177.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) z))

def Law1177 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1178.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) w))

def Law1178 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1179.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) u))

def Law1179 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1180.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) x))

def Law1180 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1181.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) y))

def Law1181 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1182.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) z))

def Law1182 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1183.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) w))

def Law1183 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1184.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) x))

def Law1184 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1185.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) y))

def Law1185 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1186.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) z))

def Law1186 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1187.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) w))

def Law1187 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1188.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) x))

def Law1188 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1189.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) y))

def Law1189 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1190.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) z))

def Law1190 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1191.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) w))

def Law1191 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1192.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) x))

def Law1192 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1193.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) y))

def Law1193 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1194.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) z))

def Law1194 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1195.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) w))

def Law1195 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1196.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) u))

def Law1196 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1197.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) x))

def Law1197 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1198.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) y))

def Law1198 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1199.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) z))

def Law1199 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1200.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) w))

def Law1200 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1201.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) u))

def Law1201 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1202.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) x))

def Law1202 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1203.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) y))

def Law1203 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1204.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) z))

def Law1204 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1205.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) w))

def Law1205 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1206.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) u))

def Law1206 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1207.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) x))

def Law1207 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1208.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) y))

def Law1208 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1209.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) z))

def Law1209 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1210.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) w))

def Law1210 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1211.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) u))

def Law1211 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1212.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) x))

def Law1212 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1213.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) y))

def Law1213 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1214.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) z))

def Law1214 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1215.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) w))

def Law1215 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1216.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) u))

def Law1216 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1217.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) x))

def Law1217 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1218.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) y))

def Law1218 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1219.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) z))

def Law1219 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1220.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) w))

def Law1220 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1221.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) u))

def Law1221 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1222.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) v))

def Law1222 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation1223.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x))

def Law1223 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1224.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y))

def Law1224 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1225.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x))

def Law1225 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1226.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y))

def Law1226 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1227.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z))

def Law1227 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1228.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x))

def Law1228 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1229.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y))

def Law1229 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1230.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z))

def Law1230 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1231.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x))

def Law1231 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1232.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y))

def Law1232 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1233.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z))

def Law1233 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1234.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x))

def Law1234 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1235.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y))

def Law1235 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1236.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z))

def Law1236 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1237.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w))

def Law1237 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1238.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x))

def Law1238 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1239.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y))

def Law1239 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1240.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z))

def Law1240 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1241.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x))

def Law1241 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1242.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y))

def Law1242 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1243.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z))

def Law1243 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1244.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x))

def Law1244 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1245.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y))

def Law1245 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1246.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z))

def Law1246 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1247.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w))

def Law1247 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1248.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x))

def Law1248 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1249.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y))

def Law1249 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1250.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z))

def Law1250 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1251.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x))

def Law1251 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1252.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y))

def Law1252 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1253.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z))

def Law1253 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1254.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x))

def Law1254 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1255.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y))

def Law1255 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1256.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z))

def Law1256 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1257.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w))

def Law1257 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1258.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x))

def Law1258 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1259.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y))

def Law1259 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1260.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z))

def Law1260 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1261.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w))

def Law1261 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1262.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x))

def Law1262 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1263.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y))

def Law1263 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1264.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z))

def Law1264 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1265.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w))

def Law1265 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1266.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x))

def Law1266 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1267.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y))

def Law1267 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1268.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z))

def Law1268 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1269.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w))

def Law1269 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1270.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x))

def Law1270 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1271.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y))

def Law1271 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1272.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z))

def Law1272 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1273.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w))

def Law1273 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1274.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u))

def Law1274 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1275.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x))

def Law1275 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1276.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y))

def Law1276 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1277.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) z))

def Law1277 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1278.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x))

def Law1278 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1279.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y))

def Law1279 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1280.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z))

def Law1280 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1281.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) x))

def Law1281 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1282.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) y))

def Law1282 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1283.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) z))

def Law1283 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1284.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) w))

def Law1284 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1285.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x))

def Law1285 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1286.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y))

def Law1286 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1287.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z))

def Law1287 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1288.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x))

def Law1288 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1289.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y))

def Law1289 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1290.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z))

def Law1290 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1291.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x))

def Law1291 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1292.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y))

def Law1292 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1293.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z))

def Law1293 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1294.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w))

def Law1294 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1295.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) x))

def Law1295 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1296.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) y))

def Law1296 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1297.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) z))

def Law1297 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1298.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) w))

def Law1298 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1299.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) x))

def Law1299 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1300.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) y))

def Law1300 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1301.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) z))

def Law1301 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1302.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) w))

def Law1302 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1303.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) x))

def Law1303 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1304.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) y))

def Law1304 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1305.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) z))

def Law1305 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1306.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) w))

def Law1306 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1307.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) x))

def Law1307 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1308.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) y))

def Law1308 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1309.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) z))

def Law1309 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1310.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) w))

def Law1310 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1311.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) u))

def Law1311 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1312.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x))

def Law1312 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1313.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y))

def Law1313 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1314.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z))

def Law1314 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1315.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x))

def Law1315 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1316.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y))

def Law1316 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1317.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z))

def Law1317 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1318.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x))

def Law1318 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1319.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y))

def Law1319 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1320.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z))

def Law1320 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1321.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w))

def Law1321 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1322.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x))

def Law1322 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1323.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y))

def Law1323 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1324.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z))

def Law1324 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1325.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x))

def Law1325 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1326.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y))

def Law1326 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1327.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z))

def Law1327 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1328.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x))

def Law1328 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1329.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y))

def Law1329 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1330.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z))

def Law1330 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1331.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w))

def Law1331 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1332.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x))

def Law1332 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1333.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y))

def Law1333 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1334.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z))

def Law1334 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1335.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w))

def Law1335 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1336.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x))

def Law1336 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1337.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y))

def Law1337 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1338.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z))

def Law1338 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1339.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w))

def Law1339 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1340.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x))

def Law1340 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1341.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y))

def Law1341 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1342.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z))

def Law1342 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1343.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w))

def Law1343 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1344.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x))

def Law1344 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1345.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y))

def Law1345 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1346.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z))

def Law1346 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1347.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w))

def Law1347 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1348.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u))

def Law1348 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1349.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) x))

def Law1349 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1350.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) y))

def Law1350 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1351.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) z))

def Law1351 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1352.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) w))

def Law1352 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1353.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) x))

def Law1353 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1354.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) y))

def Law1354 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1355.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) z))

def Law1355 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1356.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) w))

def Law1356 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1357.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) x))

def Law1357 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1358.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) y))

def Law1358 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1359.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) z))

def Law1359 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1360.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) w))

def Law1360 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1361.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) x))

def Law1361 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1362.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) y))

def Law1362 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1363.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) z))

def Law1363 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1364.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) w))

def Law1364 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1365.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) u))

def Law1365 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1366.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) x))

def Law1366 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1367.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) y))

def Law1367 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1368.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) z))

def Law1368 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1369.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) w))

def Law1369 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1370.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) x))

def Law1370 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1371.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) y))

def Law1371 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1372.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) z))

def Law1372 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1373.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) w))

def Law1373 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1374.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) x))

def Law1374 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1375.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) y))

def Law1375 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1376.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) z))

def Law1376 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1377.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) w))

def Law1377 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1378.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) x))

def Law1378 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1379.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) y))

def Law1379 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1380.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) z))

def Law1380 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1381.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) w))

def Law1381 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1382.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) u))

def Law1382 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1383.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) x))

def Law1383 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1384.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) y))

def Law1384 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1385.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) z))

def Law1385 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1386.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) w))

def Law1386 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1387.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) x))

def Law1387 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1388.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) y))

def Law1388 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1389.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) z))

def Law1389 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1390.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) w))

def Law1390 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1391.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) x))

def Law1391 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1392.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) y))

def Law1392 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1393.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) z))

def Law1393 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1394.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) w))

def Law1394 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1395.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) x))

def Law1395 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1396.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) y))

def Law1396 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1397.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) z))

def Law1397 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1398.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) w))

def Law1398 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1399.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) u))

def Law1399 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1400.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) x))

def Law1400 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1401.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) y))

def Law1401 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1402.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) z))

def Law1402 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1403.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) w))

def Law1403 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1404.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) u))

def Law1404 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1405.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) x))

def Law1405 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1406.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) y))

def Law1406 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1407.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) z))

def Law1407 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1408.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) w))

def Law1408 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1409.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) u))

def Law1409 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1410.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) x))

def Law1410 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1411.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) y))

def Law1411 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1412.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) z))

def Law1412 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1413.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) w))

def Law1413 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1414.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) u))

def Law1414 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1415.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) x))

def Law1415 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1416.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) y))

def Law1416 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1417.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) z))

def Law1417 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1418.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) w))

def Law1418 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1419.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) u))

def Law1419 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1420.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) x))

def Law1420 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1421.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) y))

def Law1421 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1422.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) z))

def Law1422 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1423.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) w))

def Law1423 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1424.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) u))

def Law1424 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1425.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) v))

def Law1425 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation1427.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law1427 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1428.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law1428 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1429.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law1429 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1430.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law1430 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1431.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law1431 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1432.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law1432 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1433.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law1433 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1434.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law1434 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1435.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law1435 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1436.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law1436 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1437.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law1437 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1438.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law1438 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1439.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law1439 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1440.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law1440 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1441.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law1441 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1442.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law1442 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1443.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law1443 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1444.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law1444 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1445.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law1445 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1446.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law1446 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1447.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law1447 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1448.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law1448 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1449.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law1449 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1450.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law1450 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1451.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law1451 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1452.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law1452 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1453.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law1453 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1454.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law1454 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1455.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law1455 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1456.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law1456 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1457.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law1457 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1458.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law1458 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1459.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law1459 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1460.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law1460 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1461.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law1461 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1462.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law1462 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1463.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law1463 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1464.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law1464 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1465.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law1465 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1466.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law1466 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1467.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law1467 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1468.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law1468 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1469.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law1469 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1470.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law1470 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1471.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law1471 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1472.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law1472 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1473.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law1473 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1474.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law1474 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1475.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law1475 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1476.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law1476 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1477.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law1477 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1478.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law1478 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1479.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law1479 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1480.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law1480 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1481.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law1481 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1482.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law1482 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1483.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law1483 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1484.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law1484 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1486.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law1486 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1487.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law1487 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1488.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law1488 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1489.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law1489 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1490.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law1490 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1492.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law1492 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1493.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law1493 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1494.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law1494 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1495.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law1495 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1496.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law1496 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1497.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law1497 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1498.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law1498 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1499.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law1499 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1500.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law1500 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1501.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law1501 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1502.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law1502 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1503.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law1503 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1504.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law1504 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1505.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law1505 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1506.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law1506 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1507.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law1507 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1508.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law1508 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1509.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law1509 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1510.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law1510 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1511.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law1511 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1512.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law1512 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1513.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law1513 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1514.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law1514 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1515.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law1515 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1516.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law1516 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1517.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law1517 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1518.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law1518 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1519.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law1519 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1520.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law1520 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1521.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law1521 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1522.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law1522 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1523.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law1523 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1524.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law1524 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1525.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law1525 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1526.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law1526 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1527.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law1527 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1528.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law1528 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1529.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law1529 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1530.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law1530 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1531.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law1531 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1532.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law1532 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1533.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law1533 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1534.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law1534 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1535.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law1535 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1536.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law1536 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1537.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law1537 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1538.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law1538 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1539.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law1539 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1540.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law1540 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1541.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law1541 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1542.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law1542 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1543.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law1543 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1544.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law1544 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1545.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law1545 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1546.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law1546 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1547.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law1547 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1548.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law1548 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1549.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law1549 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1550.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law1550 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1551.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law1551 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1552.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law1552 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1553.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law1553 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1554.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law1554 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1555.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x w)))

def Law1555 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1556.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law1556 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1557.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law1557 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1558.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law1558 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1559.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y w)))

def Law1559 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1560.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law1560 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1561.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law1561 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1562.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law1562 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1563.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law1563 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1564.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w x)))

def Law1564 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1565.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w y)))

def Law1565 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1566.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w z)))

def Law1566 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1567.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w w)))

def Law1567 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1568.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w u)))

def Law1568 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1569.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law1569 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1570.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law1570 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1572.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x w)))

def Law1572 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1573.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law1573 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1574.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law1574 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1575.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law1575 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1576.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y w)))

def Law1576 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1577.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law1577 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1578.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law1578 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1579.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law1579 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1580.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law1580 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1581.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w x)))

def Law1581 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1582.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w y)))

def Law1582 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1583.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w z)))

def Law1583 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1584.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w w)))

def Law1584 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1585.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w u)))

def Law1585 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1586.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law1586 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1587.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law1587 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1588.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law1588 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1589.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law1589 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1590.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law1590 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1591.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law1591 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1592.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law1592 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1593.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law1593 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1594.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law1594 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1595.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law1595 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1596.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law1596 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1597.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law1597 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1598.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law1598 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1599.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law1599 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1600.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law1600 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1601.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law1601 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1602.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law1602 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1603.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x x)))

def Law1603 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1604.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x y)))

def Law1604 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1605.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x z)))

def Law1605 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1606.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x w)))

def Law1606 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1607.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x u)))

def Law1607 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1608.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y x)))

def Law1608 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1609.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y y)))

def Law1609 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1610.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y z)))

def Law1610 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1611.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y w)))

def Law1611 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1612.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y u)))

def Law1612 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1613.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z x)))

def Law1613 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1614.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z y)))

def Law1614 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1615.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z z)))

def Law1615 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1616.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z w)))

def Law1616 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1617.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z u)))

def Law1617 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1618.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w x)))

def Law1618 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1619.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w y)))

def Law1619 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1620.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w z)))

def Law1620 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1621.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w w)))

def Law1621 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1622.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w u)))

def Law1622 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1623.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u x)))

def Law1623 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1624.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u y)))

def Law1624 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1625.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u z)))

def Law1625 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1626.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u w)))

def Law1626 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation1627.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u u)))

def Law1627 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation1628.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u v)))

def Law1628 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))

abbrev Equation1629.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law1629 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1630.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law1630 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1631.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law1631 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1632.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law1632 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1633.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law1633 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1634.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law1634 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1635.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law1635 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1636.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law1636 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1637.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law1637 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1638.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law1638 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1639.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law1639 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1640.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law1640 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1641.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law1641 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1642.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law1642 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1643.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law1643 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1644.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law1644 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1645.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law1645 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1646.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law1646 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1647.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law1647 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1648.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law1648 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1649.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law1649 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1650.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law1650 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1651.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law1651 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1652.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law1652 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1653.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law1653 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1654.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law1654 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1655.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law1655 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1656.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law1656 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1657.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law1657 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1658.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law1658 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1660.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law1660 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1662.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law1662 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1663.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law1663 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1664.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law1664 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1665.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law1665 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1666.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law1666 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1667.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law1667 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1668.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law1668 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1669.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law1669 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1670.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law1670 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1671.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law1671 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1672.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law1672 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1673.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law1673 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1674.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law1674 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1675.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law1675 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1676.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law1676 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1677.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law1677 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1678.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law1678 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1679.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law1679 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1680.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law1680 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1681.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law1681 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1682.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law1682 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1683.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law1683 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1684.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law1684 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1685.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law1685 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1686.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law1686 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1687.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law1687 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1688.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law1688 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1690.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law1690 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1691.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law1691 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1692.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law1692 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1693.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law1693 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1694.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law1694 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1695.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law1695 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1696.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law1696 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1697.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law1697 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1698.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law1698 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1699.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law1699 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1700.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law1700 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1702.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law1702 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1703.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law1703 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1704.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law1704 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1705.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law1705 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1706.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law1706 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1707.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law1707 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1708.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law1708 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1709.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law1709 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1710.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law1710 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1711.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law1711 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1712.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law1712 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1713.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law1713 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1714.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law1714 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1715.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law1715 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1716.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law1716 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1717.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law1717 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1718.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law1718 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1719.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law1719 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1720.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law1720 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1721.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law1721 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1722.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law1722 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1723.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law1723 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1724.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law1724 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1725.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law1725 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1726.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law1726 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1727.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law1727 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1728.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law1728 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1729.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law1729 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1730.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law1730 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1731.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law1731 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1732.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law1732 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1733.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law1733 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1734.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law1734 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1735.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law1735 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1736.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law1736 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1737.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law1737 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1738.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law1738 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1739.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law1739 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1740.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law1740 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1741.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law1741 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1742.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law1742 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1743.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law1743 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1744.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law1744 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1745.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law1745 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1746.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law1746 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1747.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law1747 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1748.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law1748 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1749.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law1749 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1750.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law1750 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1751.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law1751 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1752.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law1752 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1753.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law1753 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1754.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law1754 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1755.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law1755 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1756.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law1756 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1757.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law1757 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1758.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) w))

def Law1758 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1759.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law1759 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1760.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law1760 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1761.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law1761 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1762.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) w))

def Law1762 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1763.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law1763 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1764.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law1764 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1765.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law1765 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1766.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law1766 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1767.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) x))

def Law1767 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1768.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) y))

def Law1768 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1769.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) z))

def Law1769 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1770.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) w))

def Law1770 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1771.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) u))

def Law1771 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1772.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law1772 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1773.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law1773 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1774.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law1774 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1775.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) w))

def Law1775 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1776.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law1776 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1777.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law1777 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1778.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law1778 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1779.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) w))

def Law1779 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1780.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law1780 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1781.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law1781 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1782.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law1782 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1783.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law1783 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1784.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) x))

def Law1784 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1785.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) y))

def Law1785 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1786.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) z))

def Law1786 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1787.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) w))

def Law1787 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1788.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) u))

def Law1788 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1789.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law1789 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1790.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law1790 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1791.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law1791 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1792.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law1792 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1793.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law1793 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1794.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law1794 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1795.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law1795 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1796.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law1796 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1797.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law1797 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1798.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law1798 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1799.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law1799 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1800.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law1800 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1801.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law1801 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1802.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law1802 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1803.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law1803 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1804.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law1804 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1805.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law1805 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1806.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) x))

def Law1806 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1807.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) y))

def Law1807 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1808.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) z))

def Law1808 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1809.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) w))

def Law1809 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1810.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) u))

def Law1810 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1811.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) x))

def Law1811 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1812.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) y))

def Law1812 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1813.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) z))

def Law1813 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1814.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) w))

def Law1814 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1815.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) u))

def Law1815 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1816.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) x))

def Law1816 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1817.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) y))

def Law1817 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1818.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) z))

def Law1818 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1819.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) w))

def Law1819 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1820.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) u))

def Law1820 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1821.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) x))

def Law1821 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1822.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) y))

def Law1822 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1823.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) z))

def Law1823 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1824.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) w))

def Law1824 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1825.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) u))

def Law1825 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1826.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) x))

def Law1826 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1827.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) y))

def Law1827 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1828.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) z))

def Law1828 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1829.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) w))

def Law1829 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1830.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) u))

def Law1830 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1831.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) v))

def Law1831 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation1832.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst x x))

def Law1832 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1833.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst x y))

def Law1833 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1834.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y x))

def Law1834 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1835.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y y))

def Law1835 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1836.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y z))

def Law1836 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1837.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x x))

def Law1837 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1838.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x y))

def Law1838 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1839.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x z))

def Law1839 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1840.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y x))

def Law1840 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1841.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y y))

def Law1841 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1842.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y z))

def Law1842 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1843.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z x))

def Law1843 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1844.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z y))

def Law1844 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1845.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z z))

def Law1845 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1846.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z w))

def Law1846 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1847.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x x))

def Law1847 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1848.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x y))

def Law1848 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1849.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x z))

def Law1849 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1850.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y x))

def Law1850 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1851.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y y))

def Law1851 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1852.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y z))

def Law1852 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1853.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z x))

def Law1853 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1854.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z y))

def Law1854 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1855.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z z))

def Law1855 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1856.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z w))

def Law1856 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1857.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x x))

def Law1857 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1858.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x y))

def Law1858 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1859.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x z))

def Law1859 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1860.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y x))

def Law1860 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1861.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y y))

def Law1861 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1862.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y z))

def Law1862 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1863.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z x))

def Law1863 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1864.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z y))

def Law1864 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1865.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z z))

def Law1865 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1866.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z w))

def Law1866 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1867.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x x))

def Law1867 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1868.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x y))

def Law1868 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1869.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x z))

def Law1869 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1870.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x w))

def Law1870 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1871.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y x))

def Law1871 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1872.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y y))

def Law1872 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1873.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y z))

def Law1873 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1874.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y w))

def Law1874 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1875.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z x))

def Law1875 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1876.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z y))

def Law1876 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1877.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z z))

def Law1877 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1878.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z w))

def Law1878 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1879.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w x))

def Law1879 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1880.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w y))

def Law1880 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1881.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w z))

def Law1881 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1882.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w w))

def Law1882 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1883.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w u))

def Law1883 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1884.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst x x))

def Law1884 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1885.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst x y))

def Law1885 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1886.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst x z))

def Law1886 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1887.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y x))

def Law1887 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1888.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y y))

def Law1888 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1889.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst y z))

def Law1889 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1890.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst z x))

def Law1890 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1891.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst z y))

def Law1891 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1892.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst z z))

def Law1892 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1893.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) (@Magma.op.{u} G inst z w))

def Law1893 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1894.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x x))

def Law1894 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1895.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x y))

def Law1895 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1896.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst x z))

def Law1896 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1897.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y x))

def Law1897 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1898.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y y))

def Law1898 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1899.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst y z))

def Law1899 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1900.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z x))

def Law1900 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1901.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z y))

def Law1901 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1902.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z z))

def Law1902 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1903.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) (@Magma.op.{u} G inst z w))

def Law1903 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1904.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst x x))

def Law1904 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1905.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst x y))

def Law1905 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1906.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst x z))

def Law1906 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1907.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst x w))

def Law1907 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1908.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst y x))

def Law1908 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1909.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst y y))

def Law1909 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1910.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst y z))

def Law1910 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1911.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst y w))

def Law1911 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1912.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst z x))

def Law1912 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1913.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst z y))

def Law1913 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1914.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst z z))

def Law1914 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1915.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst z w))

def Law1915 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1916.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst w x))

def Law1916 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1917.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst w y))

def Law1917 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1918.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst w z))

def Law1918 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1919.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst w w))

def Law1919 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1920.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) (@Magma.op.{u} G inst w u))

def Law1920 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1921.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x x))

def Law1921 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1922.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x y))

def Law1922 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1923.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst x z))

def Law1923 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1924.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y x))

def Law1924 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1925.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y y))

def Law1925 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1926.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst y z))

def Law1926 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1927.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z x))

def Law1927 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1928.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z y))

def Law1928 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1929.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z z))

def Law1929 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1930.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) (@Magma.op.{u} G inst z w))

def Law1930 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1931.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x x))

def Law1931 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1932.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x y))

def Law1932 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1933.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst x z))

def Law1933 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1934.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y x))

def Law1934 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1935.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y y))

def Law1935 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1936.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst y z))

def Law1936 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1937.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z x))

def Law1937 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1938.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z y))

def Law1938 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1939.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z z))

def Law1939 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1940.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) (@Magma.op.{u} G inst z w))

def Law1940 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1941.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x x))

def Law1941 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1942.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x y))

def Law1942 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1943.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x z))

def Law1943 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1944.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst x w))

def Law1944 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1945.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y x))

def Law1945 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1946.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y y))

def Law1946 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1947.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y z))

def Law1947 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1948.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst y w))

def Law1948 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1949.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z x))

def Law1949 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1950.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z y))

def Law1950 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1951.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z z))

def Law1951 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1952.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst z w))

def Law1952 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1953.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w x))

def Law1953 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1954.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w y))

def Law1954 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1955.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w z))

def Law1955 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1956.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w w))

def Law1956 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1957.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) (@Magma.op.{u} G inst w u))

def Law1957 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1958.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst x x))

def Law1958 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1959.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst x y))

def Law1959 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1960.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst x z))

def Law1960 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1961.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst x w))

def Law1961 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1962.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst y x))

def Law1962 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1963.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst y y))

def Law1963 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1964.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst y z))

def Law1964 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1965.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst y w))

def Law1965 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1966.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst z x))

def Law1966 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1967.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst z y))

def Law1967 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1968.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst z z))

def Law1968 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1969.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst z w))

def Law1969 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1970.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst w x))

def Law1970 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1971.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst w y))

def Law1971 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1972.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst w z))

def Law1972 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1973.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst w w))

def Law1973 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1974.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) (@Magma.op.{u} G inst w u))

def Law1974 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1975.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst x x))

def Law1975 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1976.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst x y))

def Law1976 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1977.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst x z))

def Law1977 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1978.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst x w))

def Law1978 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1979.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst y x))

def Law1979 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1980.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst y y))

def Law1980 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1981.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst y z))

def Law1981 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1982.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst y w))

def Law1982 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1983.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst z x))

def Law1983 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1984.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst z y))

def Law1984 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1985.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst z z))

def Law1985 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1986.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst z w))

def Law1986 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1987.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst w x))

def Law1987 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1988.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst w y))

def Law1988 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1989.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst w z))

def Law1989 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1990.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst w w))

def Law1990 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1991.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) (@Magma.op.{u} G inst w u))

def Law1991 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation1992.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst x x))

def Law1992 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1993.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst x y))

def Law1993 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1994.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst x z))

def Law1994 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1995.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst x w))

def Law1995 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation1996.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst y x))

def Law1996 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation1997.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst y y))

def Law1997 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1998.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst y z))

def Law1998 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1999.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst y w))

def Law1999 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
