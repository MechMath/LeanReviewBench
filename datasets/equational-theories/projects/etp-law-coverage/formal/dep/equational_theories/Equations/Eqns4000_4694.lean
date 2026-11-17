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

abbrev Equation4000.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) x)

def Law4000 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4001.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) y)

def Law4001 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4002.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) z)

def Law4002 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4003.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) w)

def Law4003 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4004.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)) u)

def Law4004 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4005.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) x)

def Law4005 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4006.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) y)

def Law4006 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4007.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) z)

def Law4007 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4008.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)) w)

def Law4008 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4009.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) x)

def Law4009 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4010.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) y)

def Law4010 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4011.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) z)

def Law4011 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4012.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)) w)

def Law4012 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4013.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) x)

def Law4013 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4014.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) y)

def Law4014 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4015.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) z)

def Law4015 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4016.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)) w)

def Law4016 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4017.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) x)

def Law4017 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4018.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) y)

def Law4018 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4019.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) z)

def Law4019 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4020.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) w)

def Law4020 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4021.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)) u)

def Law4021 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4022.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) x)

def Law4022 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4023.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) y)

def Law4023 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4024.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) z)

def Law4024 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4025.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)) w)

def Law4025 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4026.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) x)

def Law4026 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4027.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) y)

def Law4027 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4028.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) z)

def Law4028 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4029.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)) w)

def Law4029 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4030.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) x)

def Law4030 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4031.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) y)

def Law4031 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4032.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) z)

def Law4032 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4033.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)) w)

def Law4033 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4034.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) x)

def Law4034 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4035.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) y)

def Law4035 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4036.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) z)

def Law4036 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4037.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) w)

def Law4037 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4038.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)) u)

def Law4038 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4039.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) x)

def Law4039 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4040.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) y)

def Law4040 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4041.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) z)

def Law4041 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4042.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) w)

def Law4042 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4043.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)) u)

def Law4043 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4044.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) x)

def Law4044 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4045.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) y)

def Law4045 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4046.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) z)

def Law4046 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4047.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) w)

def Law4047 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4048.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)) u)

def Law4048 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4049.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) x)

def Law4049 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4050.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) y)

def Law4050 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4051.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) z)

def Law4051 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4052.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) w)

def Law4052 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4053.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)) u)

def Law4053 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4054.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) x)

def Law4054 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4055.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) y)

def Law4055 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4056.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) z)

def Law4056 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4057.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) w)

def Law4057 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4058.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)) u)

def Law4058 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4059.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) x)

def Law4059 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4060.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) y)

def Law4060 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4061.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) z)

def Law4061 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4062.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) w)

def Law4062 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4063.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) u)

def Law4063 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4064.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)) v)

def Law4064 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation4066.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y)

def Law4066 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4067.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x)

def Law4067 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4068.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y)

def Law4068 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4069.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z)

def Law4069 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4070.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x)

def Law4070 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4071.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y)

def Law4071 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4072.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z)

def Law4072 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4073.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x)

def Law4073 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4074.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y)

def Law4074 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4075.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z)

def Law4075 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4076.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x)

def Law4076 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4077.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y)

def Law4077 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4078.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z)

def Law4078 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4079.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w)

def Law4079 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4080.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x)

def Law4080 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4081.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y)

def Law4081 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4082.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z)

def Law4082 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4083.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x)

def Law4083 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4084.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y)

def Law4084 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4085.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z)

def Law4085 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4086.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x)

def Law4086 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4087.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y)

def Law4087 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4088.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z)

def Law4088 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4089.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w)

def Law4089 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4090.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x)

def Law4090 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4091.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y)

def Law4091 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4092.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z)

def Law4092 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4093.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x)

def Law4093 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4094.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y)

def Law4094 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4095.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z)

def Law4095 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4096.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x)

def Law4096 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4097.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y)

def Law4097 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4098.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z)

def Law4098 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4099.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w)

def Law4099 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4100.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x)

def Law4100 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4101.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y)

def Law4101 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4102.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z)

def Law4102 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4103.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w)

def Law4103 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4104.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x)

def Law4104 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4105.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y)

def Law4105 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4106.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z)

def Law4106 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4107.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w)

def Law4107 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4108.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x)

def Law4108 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4109.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y)

def Law4109 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4110.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z)

def Law4110 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4111.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w)

def Law4111 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4112.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x)

def Law4112 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4113.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y)

def Law4113 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4114.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z)

def Law4114 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4115.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w)

def Law4115 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4116.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u)

def Law4116 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4117.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x)

def Law4117 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4118.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y)

def Law4118 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4119.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) z)

def Law4119 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4120.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x)

def Law4120 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4121.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y)

def Law4121 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4122.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z)

def Law4122 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4123.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) x)

def Law4123 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4124.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) y)

def Law4124 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4125.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) z)

def Law4125 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4126.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z) w)

def Law4126 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4127.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x)

def Law4127 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4128.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y)

def Law4128 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4129.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z)

def Law4129 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4130.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x)

def Law4130 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4131.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y)

def Law4131 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4132.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z)

def Law4132 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4133.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x)

def Law4133 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4134.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y)

def Law4134 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4135.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z)

def Law4135 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4136.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w)

def Law4136 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4137.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) x)

def Law4137 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4138.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) y)

def Law4138 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4139.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) z)

def Law4139 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4140.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x) w)

def Law4140 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4141.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) x)

def Law4141 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4142.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) y)

def Law4142 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4143.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) z)

def Law4143 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4144.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y) w)

def Law4144 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4145.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) x)

def Law4145 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4146.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) y)

def Law4146 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4147.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) z)

def Law4147 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4148.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z) w)

def Law4148 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4149.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) x)

def Law4149 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4150.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) y)

def Law4150 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4151.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) z)

def Law4151 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4152.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) w)

def Law4152 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4153.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w) u)

def Law4153 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4154.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x)

def Law4154 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4155.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y)

def Law4155 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4156.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z)

def Law4156 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4157.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x)

def Law4157 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4158.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y)

def Law4158 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4159.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z)

def Law4159 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4160.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x)

def Law4160 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4161.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y)

def Law4161 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4162.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z)

def Law4162 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4163.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w)

def Law4163 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4164.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x)

def Law4164 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4165.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y)

def Law4165 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4166.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z)

def Law4166 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4167.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x)

def Law4167 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4168.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y)

def Law4168 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4169.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z)

def Law4169 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4170.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x)

def Law4170 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4171.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y)

def Law4171 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4172.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z)

def Law4172 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4173.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w)

def Law4173 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4174.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x)

def Law4174 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4175.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y)

def Law4175 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4176.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z)

def Law4176 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4177.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w)

def Law4177 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4178.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x)

def Law4178 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4179.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y)

def Law4179 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4180.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z)

def Law4180 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4181.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w)

def Law4181 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4182.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x)

def Law4182 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4183.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y)

def Law4183 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4184.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z)

def Law4184 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4185.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w)

def Law4185 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4186.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x)

def Law4186 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4187.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y)

def Law4187 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4188.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z)

def Law4188 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4189.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w)

def Law4189 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4190.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u)

def Law4190 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4191.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) x)

def Law4191 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4192.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) y)

def Law4192 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4193.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) z)

def Law4193 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4194.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x) w)

def Law4194 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4195.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) x)

def Law4195 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4196.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) y)

def Law4196 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4197.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) z)

def Law4197 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4198.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y) w)

def Law4198 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4199.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) x)

def Law4199 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4200.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) y)

def Law4200 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4201.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) z)

def Law4201 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4202.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z) w)

def Law4202 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4203.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) x)

def Law4203 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4204.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) y)

def Law4204 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4205.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) z)

def Law4205 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4206.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) w)

def Law4206 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4207.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w) u)

def Law4207 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4208.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) x)

def Law4208 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4209.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) y)

def Law4209 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4210.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) z)

def Law4210 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4211.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x) w)

def Law4211 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4212.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) x)

def Law4212 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4213.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) y)

def Law4213 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4214.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) z)

def Law4214 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4215.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y) w)

def Law4215 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4216.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) x)

def Law4216 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4217.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) y)

def Law4217 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4218.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) z)

def Law4218 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4219.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z) w)

def Law4219 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4220.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) x)

def Law4220 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4221.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) y)

def Law4221 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4222.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) z)

def Law4222 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4223.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) w)

def Law4223 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4224.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w) u)

def Law4224 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4225.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) x)

def Law4225 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4226.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) y)

def Law4226 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4227.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) z)

def Law4227 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4228.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x) w)

def Law4228 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4229.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) x)

def Law4229 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4230.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) y)

def Law4230 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4231.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) z)

def Law4231 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4232.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y) w)

def Law4232 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4233.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) x)

def Law4233 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4234.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) y)

def Law4234 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4235.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) z)

def Law4235 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4236.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z) w)

def Law4236 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4237.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) x)

def Law4237 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4238.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) y)

def Law4238 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4239.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) z)

def Law4239 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4240.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) w)

def Law4240 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4241.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w) u)

def Law4241 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4242.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) x)

def Law4242 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4243.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) y)

def Law4243 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4244.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) z)

def Law4244 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4245.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) w)

def Law4245 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4246.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x) u)

def Law4246 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4247.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) x)

def Law4247 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4248.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) y)

def Law4248 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4249.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) z)

def Law4249 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4250.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) w)

def Law4250 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4251.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y) u)

def Law4251 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4252.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) x)

def Law4252 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4253.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) y)

def Law4253 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4254.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) z)

def Law4254 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4255.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) w)

def Law4255 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4256.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z) u)

def Law4256 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4257.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) x)

def Law4257 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4258.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) y)

def Law4258 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4259.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) z)

def Law4259 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4260.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) w)

def Law4260 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4261.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w) u)

def Law4261 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4262.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) x)

def Law4262 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4263.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) y)

def Law4263 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4264.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) z)

def Law4264 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4265.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) w)

def Law4265 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4266.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) u)

def Law4266 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4267.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u) v)

def Law4267 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation4268.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))

def Law4268 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4269.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))

def Law4269 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4270.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))

def Law4270 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4271.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))

def Law4271 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4272.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))

def Law4272 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4273.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))

def Law4273 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4274.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))

def Law4274 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4275.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))

def Law4275 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4276.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y))

def Law4276 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4277.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))

def Law4277 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4278.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))

def Law4278 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4279.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))

def Law4279 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4280.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))

def Law4280 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4281.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))

def Law4281 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4282.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z))

def Law4282 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4283.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))

def Law4283 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4284.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))

def Law4284 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4285.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))

def Law4285 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4286.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))

def Law4286 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4287.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))

def Law4287 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4288.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))

def Law4288 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4289.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))

def Law4289 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4290.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))

def Law4290 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4291.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))

def Law4291 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4292.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))

def Law4292 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4293.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))

def Law4293 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4294.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z))

def Law4294 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4295.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))

def Law4295 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4296.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))

def Law4296 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4297.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))

def Law4297 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4298.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))

def Law4298 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4299.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))

def Law4299 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4300.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))

def Law4300 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4301.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z))

def Law4301 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4302.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))

def Law4302 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4303.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))

def Law4303 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4304.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))

def Law4304 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4305.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))

def Law4305 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4306.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))

def Law4306 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4307.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y))

def Law4307 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4308.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w))

def Law4308 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4309.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))

def Law4309 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4310.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))

def Law4310 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4311.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))

def Law4311 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4312.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))

def Law4312 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4313.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))

def Law4313 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4314.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))

def Law4314 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4316.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x))

def Law4316 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4317.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))

def Law4317 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4318.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))

def Law4318 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4319.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))

def Law4319 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4320.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))

def Law4320 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4321.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))

def Law4321 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4322.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))

def Law4322 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4323.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))

def Law4323 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4324.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y))

def Law4324 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4325.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))

def Law4325 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4326.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))

def Law4326 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4327.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x))

def Law4327 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4328.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))

def Law4328 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4329.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))

def Law4329 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4330.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))

def Law4330 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4331.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))

def Law4331 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4332.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z))

def Law4332 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4333.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))

def Law4333 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4334.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))

def Law4334 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4335.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))

def Law4335 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4336.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z))

def Law4336 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4337.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))

def Law4337 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4338.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))

def Law4338 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4339.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))

def Law4339 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4340.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))

def Law4340 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4341.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z))

def Law4341 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4342.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))

def Law4342 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4343.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x))

def Law4343 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4344.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))

def Law4344 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4345.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))

def Law4345 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4346.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z))

def Law4346 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4347.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))

def Law4347 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4348.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y))

def Law4348 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4349.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w))

def Law4349 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4350.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))

def Law4350 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4351.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y))

def Law4351 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4352.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))

def Law4352 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4353.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))

def Law4353 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4354.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))

def Law4354 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4355.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w))

def Law4355 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4356.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))

def Law4356 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4357.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y w))

def Law4357 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4358.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y))

def Law4358 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4359.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w))

def Law4359 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4360.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w z))

def Law4360 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4361.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w u))

def Law4361 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4362.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z))

def Law4362 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4363.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x w))

def Law4363 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4364.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x))

def Law4364 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4365.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w))

def Law4365 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4366.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w x))

def Law4366 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4367.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w z))

def Law4367 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4368.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w u))

def Law4368 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4369.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x))

def Law4369 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4370.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w))

def Law4370 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation4371.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x))

def Law4371 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation4372.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y))

def Law4372 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4373.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u))

def Law4373 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4374.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y z))

def Law4374 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4375.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y u))

def Law4375 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4376.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z y))

def Law4376 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation4377.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z u))

def Law4377 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation4378.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u z))

def Law4378 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4379.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u v))

def Law4379 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation4380.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law4380 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4381.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4381 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4382.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4382 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4383.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4383 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4384.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4384 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4385.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4385 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4386.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4386 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4387.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4387 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4388.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4388 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4389.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4389 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4390.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4390 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4391.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4391 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4392.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4392 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4393.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4393 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4394.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4394 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4395.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law4395 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4396.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4396 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4397.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)

def Law4397 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4398.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4398 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4399.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4399 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4400.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4400 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4401.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4401 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4402.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4402 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4403.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4403 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4404.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4404 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4405.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4405 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4406.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4406 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4407.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4407 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4408.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4408 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4409.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4409 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4410.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4410 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4411.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4411 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4412.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4412 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4413.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4413 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4414.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4414 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4415.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4415 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4416.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4416 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4417.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)

def Law4417 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4418.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4418 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4419.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4419 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4420.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4420 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4421.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4421 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4422.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4422 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4423.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)

def Law4423 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4424.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)

def Law4424 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4425.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)

def Law4425 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4426.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)

def Law4426 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4427.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4427 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4428.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4428 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4429.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4429 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4430.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4430 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4431.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4431 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4432.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law4432 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4433.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4433 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4434.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)

def Law4434 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4435.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4435 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4436.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4436 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4437.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4437 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4438.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4438 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4439.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4439 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4440.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4440 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4441.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4441 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4442.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4442 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4443.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4443 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4444.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4444 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4445.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4445 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4446.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4446 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4447.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4447 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4448.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4448 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4449.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4449 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4450.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4450 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4451.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4451 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4452.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4452 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4453.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4453 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4454.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)

def Law4454 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4455.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4455 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4456.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4456 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4457.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4457 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4458.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4458 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4459.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4459 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4460.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)

def Law4460 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4461.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)

def Law4461 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4462.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)

def Law4462 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4463.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)

def Law4463 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4464.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4464 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4465.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4465 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4466.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4466 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4467.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4467 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4468.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4468 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4469.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law4469 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4470.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4470 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4471.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)

def Law4471 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4472.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4472 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4473.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4473 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4474.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4474 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4475.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4475 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4476.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4476 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4477.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4477 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4478.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4478 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4479.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4479 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4480.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4480 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4481.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4481 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4482.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4482 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4483.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4483 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4484.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4484 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4485.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4485 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4486.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4486 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4487.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4487 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4488.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4488 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4489.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4489 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4490.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4490 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4491.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)

def Law4491 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4492.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4492 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4493.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4493 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4494.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4494 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4495.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4495 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4496.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4496 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4497.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)

def Law4497 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4498.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)

def Law4498 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4499.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)

def Law4499 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4500.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)

def Law4500 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4501.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4501 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4502.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4502 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4503.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4503 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4504.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4504 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4505.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4505 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4506.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law4506 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4507.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4507 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4508.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)

def Law4508 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4509.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) w)

def Law4509 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4510.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4510 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4511.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4511 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4514.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4514 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4515.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4515 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4516.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4516 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4517.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4517 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4518.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) x)

def Law4518 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4519.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) y)

def Law4519 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4520.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) z)

def Law4520 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4521.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) w)

def Law4521 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4523.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4523 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4524.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4524 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4525.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4525 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4526.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) w)

def Law4526 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4527.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4527 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4528.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4528 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4529.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4529 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4530.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) w)

def Law4530 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4531.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4531 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4532.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4532 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4533.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4533 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4534.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4534 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4535.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) x)

def Law4535 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4536.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) y)

def Law4536 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4537.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) z)

def Law4537 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4538.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) w)

def Law4538 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4539.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) u)

def Law4539 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4540.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4540 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4541.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4541 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4542.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)

def Law4542 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4543.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4543 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4544.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4544 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4545.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4545 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4546.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4546 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4547.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4547 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4548.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x)

def Law4548 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4549.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)

def Law4549 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4550.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z)

def Law4550 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4551.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)

def Law4551 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4552.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4552 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4553.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4553 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4554.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4554 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4555.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4555 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4556.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4556 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4557.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) x)

def Law4557 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4558.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) y)

def Law4558 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4559.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) z)

def Law4559 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4560.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) w)

def Law4560 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4561.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) u)

def Law4561 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4562.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) x)

def Law4562 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4563.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) y)

def Law4563 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4565.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) w)

def Law4565 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4566.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) u)

def Law4566 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4567.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) x)

def Law4567 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4568.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) y)

def Law4568 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4569.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) z)

def Law4569 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4570.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) w)

def Law4570 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4571.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) u)

def Law4571 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4572.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) x)

def Law4572 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4573.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) y)

def Law4573 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4574.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) z)

def Law4574 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4575.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) w)

def Law4575 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4576.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) u)

def Law4576 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4577.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) x)

def Law4577 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4578.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) y)

def Law4578 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4580.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) w)

def Law4580 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4581.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) u)

def Law4581 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4583.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)

def Law4583 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4584.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4584 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4585.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4585 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4586.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4586 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4587.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4587 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4588.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4588 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4589.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4589 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4590.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4590 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4591.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y)

def Law4591 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4592.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4592 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4593.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4593 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4594.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4594 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4595.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4595 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4596.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4596 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4597.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z)

def Law4597 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4598.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)

def Law4598 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4599.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4599 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4600.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4600 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4601.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4601 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4602.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4602 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4603.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4603 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4604.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4604 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4605.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4605 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4606.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4606 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4607.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4607 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4608.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law4608 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4609.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z)

def Law4609 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4610.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4610 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4611.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4611 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4612.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4612 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4613.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4613 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4614.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4614 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4615.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4615 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4616.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z)

def Law4616 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4617.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4617 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4618.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4618 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4619.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4619 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4620.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4620 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4621.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4621 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4622.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y)

def Law4622 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4623.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w)

def Law4623 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4624.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4624 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4625.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4625 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4626.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4626 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4627.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4627 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4628.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4628 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4629.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)

def Law4629 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4630.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4630 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4631.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x)

def Law4631 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4632.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4632 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4633.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4633 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4634.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4634 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4635.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4635 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4636.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law4636 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4637.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4637 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4638.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4638 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4639.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y)

def Law4639 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4640.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4640 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4641.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4641 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4642.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x)

def Law4642 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4643.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4643 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4644.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4644 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4645.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4645 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4646.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4646 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4647.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z)

def Law4647 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4648.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4648 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4649.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4649 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4650.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4650 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4651.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z)

def Law4651 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4652.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4652 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4653.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4653 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4654.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4654 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4655.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4655 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4656.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z)

def Law4656 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4657.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4657 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4658.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x)

def Law4658 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4659.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4659 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4660.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4660 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4661.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z)

def Law4661 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4662.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4662 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4663.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y)

def Law4663 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4664.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w)

def Law4664 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4665.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4665 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4666.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y)

def Law4666 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4667.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4667 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4668.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4668 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4669.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4669 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4670.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w)

def Law4670 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4671.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4671 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4672.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) w)

def Law4672 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4673.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law4673 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4674.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w)

def Law4674 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4675.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) z)

def Law4675 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4676.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) u)

def Law4676 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4677.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z)

def Law4677 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4678.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) w)

def Law4678 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4679.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x)

def Law4679 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4680.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w)

def Law4680 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4681.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) x)

def Law4681 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4682.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) z)

def Law4682 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4683.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) u)

def Law4683 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4684.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x)

def Law4684 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4685.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w)

def Law4685 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4686.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x)

def Law4686 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4687.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y)

def Law4687 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4688.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u)

def Law4688 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4689.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) z)

def Law4689 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4690.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) u)

def Law4690 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4691.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) y)

def Law4691 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation4692.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) u)

def Law4692 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4693.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) z)

def Law4693 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4694.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) v)

def Law4694 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
