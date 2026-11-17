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

abbrev Equation2000.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst z x))

def Law2000 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2001.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst z y))

def Law2001 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2002.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst z z))

def Law2002 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2003.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst z w))

def Law2003 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2004.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst w x))

def Law2004 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2005.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst w y))

def Law2005 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2006.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst w z))

def Law2006 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2007.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst w w))

def Law2007 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2008.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) (@Magma.op.{u} G inst w u))

def Law2008 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2009.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst x x))

def Law2009 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2010.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst x y))

def Law2010 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2011.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst x z))

def Law2011 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2012.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst x w))

def Law2012 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2013.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst x u))

def Law2013 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2014.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst y x))

def Law2014 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2015.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst y y))

def Law2015 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2016.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst y z))

def Law2016 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2017.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst y w))

def Law2017 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2018.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst y u))

def Law2018 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2019.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst z x))

def Law2019 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2020.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst z y))

def Law2020 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2021.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst z z))

def Law2021 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2022.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst z w))

def Law2022 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2023.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst z u))

def Law2023 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2024.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst w x))

def Law2024 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2025.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst w y))

def Law2025 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2026.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst w z))

def Law2026 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2027.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst w w))

def Law2027 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2028.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst w u))

def Law2028 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2029.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u x))

def Law2029 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2030.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u y))

def Law2030 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2031.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u z))

def Law2031 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2032.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u w))

def Law2032 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2033.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u u))

def Law2033 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2034.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) (@Magma.op.{u} G inst u v))

def Law2034 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation2035.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) (@Magma.op.{u} G inst x x))

def Law2035 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2036.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) (@Magma.op.{u} G inst x y))

def Law2036 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2037.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) (@Magma.op.{u} G inst y x))

def Law2037 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2038.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) (@Magma.op.{u} G inst y y))

def Law2038 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2039.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) (@Magma.op.{u} G inst y z))

def Law2039 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2040.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst x x))

def Law2040 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2041.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst x y))

def Law2041 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2042.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst x z))

def Law2042 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2043.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst y x))

def Law2043 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2044.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst y y))

def Law2044 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2045.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst y z))

def Law2045 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2046.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst z x))

def Law2046 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2047.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst z y))

def Law2047 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2048.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst z z))

def Law2048 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2049.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) (@Magma.op.{u} G inst z w))

def Law2049 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2050.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst x x))

def Law2050 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2051.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst x y))

def Law2051 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2052.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst x z))

def Law2052 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2053.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst y x))

def Law2053 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2054.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst y y))

def Law2054 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2055.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst y z))

def Law2055 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2056.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst z x))

def Law2056 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2057.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst z y))

def Law2057 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2058.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst z z))

def Law2058 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2059.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) (@Magma.op.{u} G inst z w))

def Law2059 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2060.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst x x))

def Law2060 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2061.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst x y))

def Law2061 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2062.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst x z))

def Law2062 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2063.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst y x))

def Law2063 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2064.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst y y))

def Law2064 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2065.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst y z))

def Law2065 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2066.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst z x))

def Law2066 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2067.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst z y))

def Law2067 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2068.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst z z))

def Law2068 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2069.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) (@Magma.op.{u} G inst z w))

def Law2069 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2070.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst x x))

def Law2070 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2071.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst x y))

def Law2071 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2072.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst x z))

def Law2072 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2073.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst x w))

def Law2073 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2074.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst y x))

def Law2074 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2075.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst y y))

def Law2075 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2076.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst y z))

def Law2076 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2077.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst y w))

def Law2077 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2078.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst z x))

def Law2078 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2079.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst z y))

def Law2079 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2080.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst z z))

def Law2080 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2081.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst z w))

def Law2081 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2082.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst w x))

def Law2082 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2083.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst w y))

def Law2083 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2084.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst w z))

def Law2084 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2085.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst w w))

def Law2085 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2086.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) (@Magma.op.{u} G inst w u))

def Law2086 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2087.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst x x))

def Law2087 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2088.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst x y))

def Law2088 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2089.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst x z))

def Law2089 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2090.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst y x))

def Law2090 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2091.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst y y))

def Law2091 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2092.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst y z))

def Law2092 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2093.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst z x))

def Law2093 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2094.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst z y))

def Law2094 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2095.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst z z))

def Law2095 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2096.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) (@Magma.op.{u} G inst z w))

def Law2096 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2097.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst x x))

def Law2097 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2098.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst x y))

def Law2098 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2099.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst x z))

def Law2099 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2100.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst y x))

def Law2100 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2101.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst y y))

def Law2101 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2102.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst y z))

def Law2102 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2103.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst z x))

def Law2103 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2104.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst z y))

def Law2104 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2105.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst z z))

def Law2105 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2106.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) (@Magma.op.{u} G inst z w))

def Law2106 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2107.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst x x))

def Law2107 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2108.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst x y))

def Law2108 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2109.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst x z))

def Law2109 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2110.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst x w))

def Law2110 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2111.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst y x))

def Law2111 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2112.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst y y))

def Law2112 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2113.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst y z))

def Law2113 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2114.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst y w))

def Law2114 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2115.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst z x))

def Law2115 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2116.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst z y))

def Law2116 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2117.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst z z))

def Law2117 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2118.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst z w))

def Law2118 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2119.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst w x))

def Law2119 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2120.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst w y))

def Law2120 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2121.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst w z))

def Law2121 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2122.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst w w))

def Law2122 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2123.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) (@Magma.op.{u} G inst w u))

def Law2123 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2124.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst x x))

def Law2124 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2125.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst x y))

def Law2125 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2126.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst x z))

def Law2126 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2127.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst y x))

def Law2127 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2128.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst y y))

def Law2128 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2129.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst y z))

def Law2129 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2130.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst z x))

def Law2130 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2131.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst z y))

def Law2131 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2132.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst z z))

def Law2132 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2133.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) (@Magma.op.{u} G inst z w))

def Law2133 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2134.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst x x))

def Law2134 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2135.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst x y))

def Law2135 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2136.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst x z))

def Law2136 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2137.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst y x))

def Law2137 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2138.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst y y))

def Law2138 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2139.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst y z))

def Law2139 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2140.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst z x))

def Law2140 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2141.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst z y))

def Law2141 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2142.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst z z))

def Law2142 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2143.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) (@Magma.op.{u} G inst z w))

def Law2143 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2144.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst x x))

def Law2144 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2145.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst x y))

def Law2145 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2146.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst x z))

def Law2146 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2147.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst x w))

def Law2147 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2148.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst y x))

def Law2148 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2149.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst y y))

def Law2149 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2150.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst y z))

def Law2150 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2151.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst y w))

def Law2151 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2152.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst z x))

def Law2152 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2153.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst z y))

def Law2153 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2154.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst z z))

def Law2154 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2155.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst z w))

def Law2155 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2156.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst w x))

def Law2156 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2157.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst w y))

def Law2157 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2158.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst w z))

def Law2158 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2159.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst w w))

def Law2159 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2160.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) (@Magma.op.{u} G inst w u))

def Law2160 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2161.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst x x))

def Law2161 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2163.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst x z))

def Law2163 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2164.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst x w))

def Law2164 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2165.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst y x))

def Law2165 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2166.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst y y))

def Law2166 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2167.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst y z))

def Law2167 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2168.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst y w))

def Law2168 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2169.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst z x))

def Law2169 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2170.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst z y))

def Law2170 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2171.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst z z))

def Law2171 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2172.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst z w))

def Law2172 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2173.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst w x))

def Law2173 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2174.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst w y))

def Law2174 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2175.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst w z))

def Law2175 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2176.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst w w))

def Law2176 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2177.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst w u))

def Law2177 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2178.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst x x))

def Law2178 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2179.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst x y))

def Law2179 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2180.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst x z))

def Law2180 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2181.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst x w))

def Law2181 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2182.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst y x))

def Law2182 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2183.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst y y))

def Law2183 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2184.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst y z))

def Law2184 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2185.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst y w))

def Law2185 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2186.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst z x))

def Law2186 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2187.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst z y))

def Law2187 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2188.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst z z))

def Law2188 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2189.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst z w))

def Law2189 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2190.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst w x))

def Law2190 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2191.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst w y))

def Law2191 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2192.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst w z))

def Law2192 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2193.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst w w))

def Law2193 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2194.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) (@Magma.op.{u} G inst w u))

def Law2194 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2195.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst x x))

def Law2195 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2196.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst x y))

def Law2196 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2197.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst x z))

def Law2197 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2198.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst x w))

def Law2198 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2199.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst y x))

def Law2199 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2200.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst y y))

def Law2200 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2201.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst y z))

def Law2201 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2202.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst y w))

def Law2202 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2203.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst z x))

def Law2203 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2204.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst z y))

def Law2204 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2205.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst z z))

def Law2205 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2206.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst z w))

def Law2206 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2207.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst w x))

def Law2207 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2208.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst w y))

def Law2208 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2209.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst w z))

def Law2209 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2210.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst w w))

def Law2210 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2211.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) (@Magma.op.{u} G inst w u))

def Law2211 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2212.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst x x))

def Law2212 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2213.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst x y))

def Law2213 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2214.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst x z))

def Law2214 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2215.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst x w))

def Law2215 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2216.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst x u))

def Law2216 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2217.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst y x))

def Law2217 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2218.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst y y))

def Law2218 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2219.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst y z))

def Law2219 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2220.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst y w))

def Law2220 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2221.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst y u))

def Law2221 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2222.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst z x))

def Law2222 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2223.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst z y))

def Law2223 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2224.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst z z))

def Law2224 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2225.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst z w))

def Law2225 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2226.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst z u))

def Law2226 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2227.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst w x))

def Law2227 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2228.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst w y))

def Law2228 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2229.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst w z))

def Law2229 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2230.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst w w))

def Law2230 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2231.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst w u))

def Law2231 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2232.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u x))

def Law2232 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2233.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u y))

def Law2233 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2234.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u z))

def Law2234 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation2235.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u w))

def Law2235 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation2236.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u u))

def Law2236 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation2237.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) (@Magma.op.{u} G inst u v))

def Law2237 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation2238.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))) x)

def Law2238 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2239.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))) y)

def Law2239 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2240.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) x)

def Law2240 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2241.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) y)

def Law2241 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2242.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) z)

def Law2242 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2243.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) x)

def Law2243 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2244.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) y)

def Law2244 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2245.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) z)

def Law2245 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2246.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) x)

def Law2246 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2247.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) y)

def Law2247 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2248.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) z)

def Law2248 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2249.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) x)

def Law2249 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2250.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) y)

def Law2250 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2251.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) z)

def Law2251 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2252.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) w)

def Law2252 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2253.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) x)

def Law2253 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2254.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) y)

def Law2254 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2255.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) z)

def Law2255 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2256.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) x)

def Law2256 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2257.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) y)

def Law2257 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2258.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) z)

def Law2258 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2259.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) x)

def Law2259 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2260.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) y)

def Law2260 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2261.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) z)

def Law2261 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2262.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) w)

def Law2262 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2263.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) x)

def Law2263 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2264.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) y)

def Law2264 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2265.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) z)

def Law2265 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2266.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) x)

def Law2266 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2267.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) y)

def Law2267 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2268.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) z)

def Law2268 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2269.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) x)

def Law2269 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2270.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) y)

def Law2270 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2271.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) z)

def Law2271 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2272.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) w)

def Law2272 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2273.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) x)

def Law2273 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2274.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) y)

def Law2274 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2275.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) z)

def Law2275 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2276.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) w)

def Law2276 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2277.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) x)

def Law2277 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2278.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) y)

def Law2278 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2279.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) z)

def Law2279 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2280.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) w)

def Law2280 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2281.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) x)

def Law2281 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2282.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) y)

def Law2282 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2283.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) z)

def Law2283 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2284.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) w)

def Law2284 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2285.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) x)

def Law2285 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2286.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) y)

def Law2286 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2287.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) z)

def Law2287 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2288.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) w)

def Law2288 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2289.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) u)

def Law2289 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2290.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))) x)

def Law2290 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2291.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))) y)

def Law2291 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2292.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))) z)

def Law2292 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2293.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) x)

def Law2293 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2294.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) y)

def Law2294 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2295.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))) z)

def Law2295 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2296.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z))) x)

def Law2296 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2297.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z))) y)

def Law2297 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2298.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z))) z)

def Law2298 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2299.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z))) w)

def Law2299 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2300.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) x)

def Law2300 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2301.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) y)

def Law2301 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2302.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))) z)

def Law2302 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2303.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) x)

def Law2303 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2304.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) y)

def Law2304 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2305.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))) z)

def Law2305 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2306.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) x)

def Law2306 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2307.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) y)

def Law2307 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2308.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) z)

def Law2308 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2309.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))) w)

def Law2309 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2310.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))) x)

def Law2310 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2311.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))) y)

def Law2311 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2312.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))) z)

def Law2312 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2313.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))) w)

def Law2313 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2314.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))) x)

def Law2314 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2315.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))) y)

def Law2315 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2316.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))) z)

def Law2316 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2317.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))) w)

def Law2317 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2318.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))) x)

def Law2318 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2319.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))) y)

def Law2319 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2320.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))) z)

def Law2320 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2321.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))) w)

def Law2321 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2322.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))) x)

def Law2322 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2323.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))) y)

def Law2323 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2324.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))) z)

def Law2324 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2325.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))) w)

def Law2325 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2326.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))) u)

def Law2326 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2327.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) x)

def Law2327 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2328.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) y)

def Law2328 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2329.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))) z)

def Law2329 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2330.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) x)

def Law2330 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2331.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) y)

def Law2331 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2332.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))) z)

def Law2332 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2333.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) x)

def Law2333 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2334.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) y)

def Law2334 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2335.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) z)

def Law2335 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2336.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))) w)

def Law2336 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2337.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) x)

def Law2337 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2338.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) y)

def Law2338 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2339.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))) z)

def Law2339 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2340.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) x)

def Law2340 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2341.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) y)

def Law2341 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2342.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))) z)

def Law2342 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2343.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) x)

def Law2343 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2344.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) y)

def Law2344 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2345.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) z)

def Law2345 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2346.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))) w)

def Law2346 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2347.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) x)

def Law2347 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2348.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) y)

def Law2348 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2349.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) z)

def Law2349 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2350.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))) w)

def Law2350 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2351.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) x)

def Law2351 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2352.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) y)

def Law2352 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2353.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) z)

def Law2353 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2354.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))) w)

def Law2354 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2355.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) x)

def Law2355 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2356.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) y)

def Law2356 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2357.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) z)

def Law2357 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2358.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))) w)

def Law2358 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2359.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) x)

def Law2359 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2360.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) y)

def Law2360 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2361.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) z)

def Law2361 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2362.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) w)

def Law2362 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2363.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))) u)

def Law2363 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2364.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))) x)

def Law2364 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2365.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))) y)

def Law2365 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2366.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))) z)

def Law2366 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2367.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))) w)

def Law2367 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2368.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))) x)

def Law2368 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2369.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))) y)

def Law2369 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2370.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))) z)

def Law2370 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2371.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))) w)

def Law2371 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2372.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z))) x)

def Law2372 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2373.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z))) y)

def Law2373 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2374.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z))) z)

def Law2374 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2375.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z))) w)

def Law2375 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2376.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))) x)

def Law2376 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2377.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))) y)

def Law2377 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2378.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))) z)

def Law2378 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2379.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))) w)

def Law2379 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2380.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))) u)

def Law2380 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2381.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))) x)

def Law2381 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2382.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))) y)

def Law2382 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2383.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))) z)

def Law2383 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2384.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))) w)

def Law2384 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2385.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))) x)

def Law2385 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2386.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))) y)

def Law2386 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2387.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))) z)

def Law2387 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2388.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))) w)

def Law2388 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2389.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))) x)

def Law2389 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2390.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))) y)

def Law2390 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2391.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))) z)

def Law2391 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2392.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))) w)

def Law2392 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2393.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))) x)

def Law2393 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2394.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))) y)

def Law2394 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2395.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))) z)

def Law2395 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2396.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))) w)

def Law2396 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2397.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))) u)

def Law2397 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2398.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x))) x)

def Law2398 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2399.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x))) y)

def Law2399 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2400.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x))) z)

def Law2400 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2401.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x))) w)

def Law2401 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2402.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y))) x)

def Law2402 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2403.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y))) y)

def Law2403 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2404.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y))) z)

def Law2404 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2405.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y))) w)

def Law2405 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2406.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z))) x)

def Law2406 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2407.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z))) y)

def Law2407 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2408.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z))) z)

def Law2408 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2409.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z))) w)

def Law2409 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2410.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))) x)

def Law2410 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2411.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))) y)

def Law2411 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2412.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))) z)

def Law2412 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2413.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))) w)

def Law2413 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2414.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))) u)

def Law2414 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2415.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))) x)

def Law2415 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2416.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))) y)

def Law2416 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2417.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))) z)

def Law2417 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2418.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))) w)

def Law2418 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2419.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))) u)

def Law2419 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2420.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))) x)

def Law2420 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2421.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))) y)

def Law2421 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2422.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))) z)

def Law2422 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2423.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))) w)

def Law2423 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2424.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))) u)

def Law2424 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2425.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))) x)

def Law2425 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2426.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))) y)

def Law2426 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2427.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))) z)

def Law2427 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2428.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))) w)

def Law2428 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2429.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))) u)

def Law2429 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2430.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))) x)

def Law2430 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2431.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))) y)

def Law2431 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2432.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))) z)

def Law2432 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2433.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))) w)

def Law2433 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2434.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))) u)

def Law2434 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2435.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) x)

def Law2435 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2436.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) y)

def Law2436 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2437.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) z)

def Law2437 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2438.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) w)

def Law2438 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2439.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) u)

def Law2439 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2440.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))) v)

def Law2440 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation2441.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)) x)

def Law2441 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2442.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)) y)

def Law2442 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2443.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) x)

def Law2443 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2444.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) y)

def Law2444 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2445.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) z)

def Law2445 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2446.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) x)

def Law2446 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2447.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) y)

def Law2447 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2448.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) z)

def Law2448 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2449.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) x)

def Law2449 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2450.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) y)

def Law2450 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2451.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) z)

def Law2451 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2452.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) x)

def Law2452 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2453.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) y)

def Law2453 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2454.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) z)

def Law2454 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2455.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) w)

def Law2455 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2456.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) x)

def Law2456 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2457.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) y)

def Law2457 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2458.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) z)

def Law2458 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2459.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) x)

def Law2459 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2460.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) y)

def Law2460 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2461.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) z)

def Law2461 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2462.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) x)

def Law2462 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2463.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) y)

def Law2463 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2464.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) z)

def Law2464 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2465.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) w)

def Law2465 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2466.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) x)

def Law2466 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2467.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) y)

def Law2467 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2468.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) z)

def Law2468 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2469.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) x)

def Law2469 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2470.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) y)

def Law2470 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2471.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) z)

def Law2471 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2472.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) x)

def Law2472 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2473.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) y)

def Law2473 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2474.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) z)

def Law2474 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2475.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) w)

def Law2475 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2476.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) x)

def Law2476 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2477.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) y)

def Law2477 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2478.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) z)

def Law2478 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2479.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) w)

def Law2479 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2480.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) x)

def Law2480 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2481.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) y)

def Law2481 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2482.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) z)

def Law2482 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2483.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) w)

def Law2483 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2484.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) x)

def Law2484 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2485.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) y)

def Law2485 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2486.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) z)

def Law2486 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2487.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) w)

def Law2487 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2488.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) x)

def Law2488 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2489.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) y)

def Law2489 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2490.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) z)

def Law2490 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2491.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) w)

def Law2491 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2492.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) u)

def Law2492 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2493.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)) x)

def Law2493 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2494.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)) y)

def Law2494 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2495.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)) z)

def Law2495 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2496.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) x)

def Law2496 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2497.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) y)

def Law2497 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2498.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)) z)

def Law2498 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2499.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)) x)

def Law2499 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2500.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)) y)

def Law2500 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2501.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)) z)

def Law2501 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2502.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)) w)

def Law2502 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2503.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) x)

def Law2503 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2504.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) y)

def Law2504 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2505.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)) z)

def Law2505 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2506.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) x)

def Law2506 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2507.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) y)

def Law2507 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2508.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)) z)

def Law2508 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2509.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) x)

def Law2509 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2510.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) y)

def Law2510 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2511.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) z)

def Law2511 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2512.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)) w)

def Law2512 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2513.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)) x)

def Law2513 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2514.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)) y)

def Law2514 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2515.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)) z)

def Law2515 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2516.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)) w)

def Law2516 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2517.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)) x)

def Law2517 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2518.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)) y)

def Law2518 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2519.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)) z)

def Law2519 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2520.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)) w)

def Law2520 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2521.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)) x)

def Law2521 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2522.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)) y)

def Law2522 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2523.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)) z)

def Law2523 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2524.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)) w)

def Law2524 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2525.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)) x)

def Law2525 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2526.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)) y)

def Law2526 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2527.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)) z)

def Law2527 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2528.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)) w)

def Law2528 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2529.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)) u)

def Law2529 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2530.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) x)

def Law2530 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2531.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) y)

def Law2531 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2532.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)) z)

def Law2532 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2533.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) x)

def Law2533 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2534.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) y)

def Law2534 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2535.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)) z)

def Law2535 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2536.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) x)

def Law2536 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2537.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) y)

def Law2537 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2538.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) z)

def Law2538 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2539.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)) w)

def Law2539 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2540.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) x)

def Law2540 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2541.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) y)

def Law2541 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2542.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)) z)

def Law2542 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2543.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) x)

def Law2543 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2544.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) y)

def Law2544 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2545.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)) z)

def Law2545 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2546.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) x)

def Law2546 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2547.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) y)

def Law2547 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2548.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) z)

def Law2548 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2549.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)) w)

def Law2549 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2550.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) x)

def Law2550 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2551.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) y)

def Law2551 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2552.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) z)

def Law2552 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2553.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)) w)

def Law2553 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2554.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) x)

def Law2554 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2555.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) y)

def Law2555 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2556.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) z)

def Law2556 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2557.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)) w)

def Law2557 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2558.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) x)

def Law2558 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2559.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) y)

def Law2559 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2560.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) z)

def Law2560 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2561.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)) w)

def Law2561 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2562.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) x)

def Law2562 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2563.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) y)

def Law2563 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2564.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) z)

def Law2564 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2565.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) w)

def Law2565 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2566.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)) u)

def Law2566 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2567.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)) x)

def Law2567 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2568.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)) y)

def Law2568 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2569.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)) z)

def Law2569 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2570.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)) w)

def Law2570 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2571.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)) x)

def Law2571 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2572.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)) y)

def Law2572 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2573.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)) z)

def Law2573 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2574.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)) w)

def Law2574 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2575.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)) x)

def Law2575 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2576.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)) y)

def Law2576 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2577.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)) z)

def Law2577 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2578.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)) w)

def Law2578 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2579.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)) x)

def Law2579 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2580.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)) y)

def Law2580 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2581.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)) z)

def Law2581 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2582.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)) w)

def Law2582 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2583.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)) u)

def Law2583 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2584.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)) x)

def Law2584 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2585.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)) y)

def Law2585 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2586.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)) z)

def Law2586 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2587.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)) w)

def Law2587 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2588.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)) x)

def Law2588 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2589.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)) y)

def Law2589 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2590.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)) z)

def Law2590 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2591.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)) w)

def Law2591 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2592.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)) x)

def Law2592 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2593.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)) y)

def Law2593 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2594.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)) z)

def Law2594 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2595.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)) w)

def Law2595 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2596.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)) x)

def Law2596 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2597.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)) y)

def Law2597 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2598.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)) z)

def Law2598 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2599.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)) w)

def Law2599 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2600.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)) u)

def Law2600 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2601.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)) x)

def Law2601 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2602.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)) y)

def Law2602 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2603.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)) z)

def Law2603 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2604.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)) w)

def Law2604 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2605.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)) x)

def Law2605 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2606.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)) y)

def Law2606 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2607.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)) z)

def Law2607 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2608.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)) w)

def Law2608 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2609.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)) x)

def Law2609 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2610.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)) y)

def Law2610 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2611.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)) z)

def Law2611 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2612.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)) w)

def Law2612 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2613.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)) x)

def Law2613 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2614.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)) y)

def Law2614 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2615.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)) z)

def Law2615 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2616.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)) w)

def Law2616 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2617.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)) u)

def Law2617 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2618.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)) x)

def Law2618 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2619.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)) y)

def Law2619 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2620.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)) z)

def Law2620 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2621.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)) w)

def Law2621 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2622.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)) u)

def Law2622 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2623.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)) x)

def Law2623 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2624.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)) y)

def Law2624 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2625.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)) z)

def Law2625 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2626.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)) w)

def Law2626 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2627.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)) u)

def Law2627 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2628.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)) x)

def Law2628 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2629.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)) y)

def Law2629 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2630.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)) z)

def Law2630 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2631.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)) w)

def Law2631 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2632.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)) u)

def Law2632 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2633.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)) x)

def Law2633 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2634.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)) y)

def Law2634 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2635.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)) z)

def Law2635 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2636.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)) w)

def Law2636 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2637.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)) u)

def Law2637 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2638.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) x)

def Law2638 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2639.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) y)

def Law2639 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2640.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) z)

def Law2640 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2641.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) w)

def Law2641 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2642.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) u)

def Law2642 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2643.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)) v)

def Law2643 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation2644.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x x)) x)

def Law2644 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2645.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x x)) y)

def Law2645 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2646.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y)) x)

def Law2646 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2647.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y)) y)

def Law2647 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2648.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y)) z)

def Law2648 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2649.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x)) x)

def Law2649 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2650.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x)) y)

def Law2650 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2651.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x)) z)

def Law2651 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2652.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y)) x)

def Law2652 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2653.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y)) y)

def Law2653 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2654.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y)) z)

def Law2654 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2655.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z)) x)

def Law2655 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2656.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z)) y)

def Law2656 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2657.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z)) z)

def Law2657 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2658.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z)) w)

def Law2658 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2659.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x x)) x)

def Law2659 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2660.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x x)) y)

def Law2660 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2661.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x x)) z)

def Law2661 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2663.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x y)) y)

def Law2663 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2664.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x y)) z)

def Law2664 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2665.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z)) x)

def Law2665 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2666.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z)) y)

def Law2666 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2667.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z)) z)

def Law2667 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2668.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z)) w)

def Law2668 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2669.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x)) x)

def Law2669 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2670.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x)) y)

def Law2670 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2671.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x)) z)

def Law2671 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2672.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y y)) x)

def Law2672 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2673.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y y)) y)

def Law2673 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2674.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y y)) z)

def Law2674 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2675.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z)) x)

def Law2675 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2676.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z)) y)

def Law2676 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2677.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z)) z)

def Law2677 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2678.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z)) w)

def Law2678 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2679.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x)) x)

def Law2679 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2680.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x)) y)

def Law2680 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2681.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x)) z)

def Law2681 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2682.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x)) w)

def Law2682 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2683.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y)) x)

def Law2683 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2684.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y)) y)

def Law2684 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2685.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y)) z)

def Law2685 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2686.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y)) w)

def Law2686 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2687.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z)) x)

def Law2687 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2688.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z)) y)

def Law2688 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2689.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z)) z)

def Law2689 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2690.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z)) w)

def Law2690 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2691.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)) x)

def Law2691 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2692.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)) y)

def Law2692 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2693.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)) z)

def Law2693 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2694.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)) w)

def Law2694 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2695.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)) u)

def Law2695 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2696.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x x)) x)

def Law2696 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2697.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x x)) y)

def Law2697 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2698.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x x)) z)

def Law2698 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2699.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x y)) x)

def Law2699 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2700.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x y)) y)

def Law2700 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2701.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x y)) z)

def Law2701 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2702.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z)) x)

def Law2702 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2703.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z)) y)

def Law2703 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2704.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z)) z)

def Law2704 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2705.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z)) w)

def Law2705 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2706.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y x)) x)

def Law2706 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2707.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y x)) y)

def Law2707 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2708.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y x)) z)

def Law2708 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2709.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y y)) x)

def Law2709 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2710.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y y)) y)

def Law2710 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2711.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y y)) z)

def Law2711 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2712.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z)) x)

def Law2712 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2713.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z)) y)

def Law2713 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2714.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z)) z)

def Law2714 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2715.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z)) w)

def Law2715 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2716.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x)) x)

def Law2716 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2717.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x)) y)

def Law2717 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2718.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x)) z)

def Law2718 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2719.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x)) w)

def Law2719 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2720.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y)) x)

def Law2720 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2721.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y)) y)

def Law2721 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2722.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y)) z)

def Law2722 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2723.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y)) w)

def Law2723 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2724.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z)) x)

def Law2724 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2725.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z)) y)

def Law2725 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2726.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z)) z)

def Law2726 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2727.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z)) w)

def Law2727 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2728.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w)) x)

def Law2728 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2729.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w)) y)

def Law2729 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2730.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w)) z)

def Law2730 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2731.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w)) w)

def Law2731 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2732.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w)) u)

def Law2732 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2733.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x x)) x)

def Law2733 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2734.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x x)) y)

def Law2734 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2735.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x x)) z)

def Law2735 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2736.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x y)) x)

def Law2736 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2737.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x y)) y)

def Law2737 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2738.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x y)) z)

def Law2738 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2739.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z)) x)

def Law2739 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2740.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z)) y)

def Law2740 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2741.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z)) z)

def Law2741 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2742.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z)) w)

def Law2742 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2743.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y x)) x)

def Law2743 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2744.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y x)) y)

def Law2744 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2745.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y x)) z)

def Law2745 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2746.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y y)) x)

def Law2746 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2747.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y y)) y)

def Law2747 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2748.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y y)) z)

def Law2748 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2749.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z)) x)

def Law2749 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2750.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z)) y)

def Law2750 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2751.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z)) z)

def Law2751 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2752.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z)) w)

def Law2752 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2753.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x)) x)

def Law2753 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2754.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x)) y)

def Law2754 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2755.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x)) z)

def Law2755 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2756.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x)) w)

def Law2756 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2757.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y)) x)

def Law2757 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2758.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y)) y)

def Law2758 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2759.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y)) z)

def Law2759 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2760.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y)) w)

def Law2760 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2761.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z)) x)

def Law2761 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2762.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z)) y)

def Law2762 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2763.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z)) z)

def Law2763 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2764.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z)) w)

def Law2764 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2765.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w)) x)

def Law2765 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2766.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w)) y)

def Law2766 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2767.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w)) z)

def Law2767 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2768.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w)) w)

def Law2768 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2769.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w)) u)

def Law2769 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2770.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x)) x)

def Law2770 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2771.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x)) y)

def Law2771 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2772.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x)) z)

def Law2772 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2773.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x)) w)

def Law2773 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2774.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y)) x)

def Law2774 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2775.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y)) y)

def Law2775 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2776.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y)) z)

def Law2776 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2777.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y)) w)

def Law2777 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2778.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z)) x)

def Law2778 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2779.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z)) y)

def Law2779 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2780.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z)) z)

def Law2780 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2781.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z)) w)

def Law2781 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2782.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w)) x)

def Law2782 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2783.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w)) y)

def Law2783 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2784.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w)) z)

def Law2784 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2785.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w)) w)

def Law2785 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2786.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w)) u)

def Law2786 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2787.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x)) x)

def Law2787 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2788.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x)) y)

def Law2788 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2789.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x)) z)

def Law2789 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2790.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x)) w)

def Law2790 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2791.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y)) x)

def Law2791 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2792.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y)) y)

def Law2792 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2793.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y)) z)

def Law2793 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2794.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y)) w)

def Law2794 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2795.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z)) x)

def Law2795 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2796.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z)) y)

def Law2796 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2797.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z)) z)

def Law2797 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2798.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z)) w)

def Law2798 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2799.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w)) x)

def Law2799 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2800.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w)) y)

def Law2800 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2801.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w)) z)

def Law2801 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2802.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w)) w)

def Law2802 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2803.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w)) u)

def Law2803 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2804.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x)) x)

def Law2804 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2805.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x)) y)

def Law2805 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2806.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x)) z)

def Law2806 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2807.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x)) w)

def Law2807 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2808.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y)) x)

def Law2808 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2809.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y)) y)

def Law2809 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2810.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y)) z)

def Law2810 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2811.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y)) w)

def Law2811 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2812.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z)) x)

def Law2812 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2813.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z)) y)

def Law2813 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2814.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z)) z)

def Law2814 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2815.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z)) w)

def Law2815 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2816.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w)) x)

def Law2816 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2817.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w)) y)

def Law2817 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2818.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w)) z)

def Law2818 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2819.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w)) w)

def Law2819 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2820.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w)) u)

def Law2820 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2821.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x)) x)

def Law2821 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2822.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x)) y)

def Law2822 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2823.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x)) z)

def Law2823 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2824.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x)) w)

def Law2824 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2825.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x)) u)

def Law2825 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2826.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y)) x)

def Law2826 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2827.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y)) y)

def Law2827 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2828.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y)) z)

def Law2828 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2829.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y)) w)

def Law2829 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2830.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y)) u)

def Law2830 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2831.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z)) x)

def Law2831 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2832.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z)) y)

def Law2832 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2833.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z)) z)

def Law2833 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2834.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z)) w)

def Law2834 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2835.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z)) u)

def Law2835 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2836.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w)) x)

def Law2836 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2837.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w)) y)

def Law2837 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2838.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w)) z)

def Law2838 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2839.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w)) w)

def Law2839 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2840.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w)) u)

def Law2840 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2841.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) x)

def Law2841 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2842.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) y)

def Law2842 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2843.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) z)

def Law2843 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2844.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) w)

def Law2844 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2845.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) u)

def Law2845 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2846.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u)) v)

def Law2846 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation2847.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x) x)

def Law2847 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2848.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x) y)

def Law2848 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2849.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y) x)

def Law2849 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2850.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y) y)

def Law2850 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2851.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y) z)

def Law2851 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2852.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x) x)

def Law2852 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2853.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x) y)

def Law2853 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2854.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x) z)

def Law2854 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2855.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y) x)

def Law2855 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2856.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y) y)

def Law2856 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2857.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y) z)

def Law2857 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2858.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z) x)

def Law2858 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2859.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z) y)

def Law2859 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2860.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z) z)

def Law2860 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2861.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z) w)

def Law2861 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2862.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x) x)

def Law2862 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2863.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x) y)

def Law2863 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2864.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x) z)

def Law2864 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2865.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y) x)

def Law2865 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2866.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y) y)

def Law2866 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2867.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y) z)

def Law2867 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2868.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z) x)

def Law2868 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2869.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z) y)

def Law2869 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2870.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z) z)

def Law2870 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2871.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z) w)

def Law2871 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2872.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x) x)

def Law2872 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2873.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x) y)

def Law2873 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2874.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x) z)

def Law2874 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2875.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y) x)

def Law2875 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2876.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y) y)

def Law2876 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2877.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y) z)

def Law2877 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2878.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z) x)

def Law2878 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2879.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z) y)

def Law2879 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2880.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z) z)

def Law2880 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2881.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z) w)

def Law2881 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2882.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x) x)

def Law2882 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2883.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x) y)

def Law2883 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2884.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x) z)

def Law2884 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2885.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x) w)

def Law2885 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2886.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y) x)

def Law2886 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2887.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y) y)

def Law2887 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2888.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y) z)

def Law2888 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2889.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y) w)

def Law2889 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2890.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z) x)

def Law2890 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2891.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z) y)

def Law2891 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2892.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z) z)

def Law2892 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2893.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z) w)

def Law2893 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2894.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w) x)

def Law2894 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2895.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w) y)

def Law2895 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2896.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w) z)

def Law2896 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2897.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w) w)

def Law2897 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2898.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w) u)

def Law2898 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2899.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x) x)

def Law2899 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2900.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x) y)

def Law2900 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2901.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x) z)

def Law2901 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2902.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y) x)

def Law2902 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2903.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y) y)

def Law2903 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2904.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y) z)

def Law2904 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2905.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z) x)

def Law2905 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2906.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z) y)

def Law2906 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2907.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z) z)

def Law2907 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2908.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z) w)

def Law2908 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2909.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x) x)

def Law2909 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2910.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x) y)

def Law2910 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2911.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x) z)

def Law2911 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2912.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y) x)

def Law2912 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2913.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y) y)

def Law2913 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2914.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y) z)

def Law2914 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2915.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z) x)

def Law2915 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2916.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z) y)

def Law2916 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2917.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z) z)

def Law2917 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2918.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z) w)

def Law2918 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2919.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x) x)

def Law2919 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2920.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x) y)

def Law2920 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2921.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x) z)

def Law2921 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2922.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x) w)

def Law2922 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2923.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y) x)

def Law2923 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2924.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y) y)

def Law2924 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2925.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y) z)

def Law2925 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2926.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y) w)

def Law2926 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2927.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z) x)

def Law2927 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2928.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z) y)

def Law2928 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2929.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z) z)

def Law2929 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2930.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z) w)

def Law2930 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2931.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w) x)

def Law2931 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2932.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w) y)

def Law2932 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2933.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w) z)

def Law2933 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2934.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w) w)

def Law2934 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2935.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w) u)

def Law2935 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2936.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x) x)

def Law2936 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2937.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x) y)

def Law2937 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2938.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x) z)

def Law2938 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2939.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y) x)

def Law2939 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2940.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y) y)

def Law2940 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2941.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y) z)

def Law2941 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2942.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z) x)

def Law2942 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2943.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z) y)

def Law2943 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2944.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z) z)

def Law2944 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2945.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z) w)

def Law2945 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2946.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x) x)

def Law2946 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2947.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x) y)

def Law2947 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2948.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x) z)

def Law2948 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2949.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y) x)

def Law2949 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2950.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y) y)

def Law2950 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2951.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y) z)

def Law2951 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2952.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z) x)

def Law2952 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2953.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z) y)

def Law2953 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2954.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z) z)

def Law2954 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2955.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z) w)

def Law2955 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2956.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x) x)

def Law2956 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2957.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x) y)

def Law2957 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2958.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x) z)

def Law2958 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2959.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x) w)

def Law2959 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2960.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y) x)

def Law2960 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2961.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y) y)

def Law2961 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2962.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y) z)

def Law2962 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2963.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y) w)

def Law2963 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2964.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z) x)

def Law2964 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2965.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z) y)

def Law2965 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2966.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z) z)

def Law2966 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2967.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z) w)

def Law2967 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2968.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w) x)

def Law2968 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2969.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w) y)

def Law2969 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2970.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w) z)

def Law2970 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2971.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w) w)

def Law2971 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2972.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w) u)

def Law2972 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2973.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x) x)

def Law2973 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2974.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x) y)

def Law2974 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2975.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x) z)

def Law2975 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2976.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x) w)

def Law2976 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2977.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y) x)

def Law2977 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2978.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y) y)

def Law2978 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2979.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y) z)

def Law2979 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2980.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y) w)

def Law2980 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2981.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z) x)

def Law2981 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2982.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z) y)

def Law2982 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2983.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z) z)

def Law2983 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2984.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z) w)

def Law2984 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2985.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w) x)

def Law2985 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2986.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w) y)

def Law2986 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2987.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w) z)

def Law2987 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2988.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w) w)

def Law2988 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2989.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w) u)

def Law2989 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation2990.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x) x)

def Law2990 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2991.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x) y)

def Law2991 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2992.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x) z)

def Law2992 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2993.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x) w)

def Law2993 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2994.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y) x)

def Law2994 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2995.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y) y)

def Law2995 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation2996.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y) z)

def Law2996 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation2997.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y) w)

def Law2997 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation2998.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z) x)

def Law2998 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation2999.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z) y)

def Law2999 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
