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

abbrev Equation3000.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z) z)

def Law3000 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3001.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z) w)

def Law3001 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3002.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w) x)

def Law3002 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3003.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w) y)

def Law3003 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3004.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w) z)

def Law3004 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3005.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w) w)

def Law3005 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3006.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w) u)

def Law3006 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3007.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x) x)

def Law3007 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3008.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x) y)

def Law3008 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3009.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x) z)

def Law3009 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3010.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x) w)

def Law3010 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3011.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y) x)

def Law3011 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3012.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y) y)

def Law3012 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3013.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y) z)

def Law3013 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3014.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y) w)

def Law3014 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3015.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z) x)

def Law3015 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3016.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z) y)

def Law3016 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3017.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z) z)

def Law3017 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3018.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z) w)

def Law3018 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3019.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w) x)

def Law3019 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3020.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w) y)

def Law3020 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3021.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w) z)

def Law3021 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3022.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w) w)

def Law3022 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3023.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w) u)

def Law3023 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3024.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x) x)

def Law3024 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3025.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x) y)

def Law3025 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3026.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x) z)

def Law3026 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3027.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x) w)

def Law3027 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3028.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x) u)

def Law3028 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3029.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y) x)

def Law3029 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3030.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y) y)

def Law3030 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3031.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y) z)

def Law3031 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3032.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y) w)

def Law3032 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3033.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y) u)

def Law3033 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3034.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z) x)

def Law3034 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3035.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z) y)

def Law3035 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3036.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z) z)

def Law3036 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3037.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z) w)

def Law3037 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3038.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z) u)

def Law3038 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3039.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w) x)

def Law3039 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3040.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w) y)

def Law3040 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3041.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w) z)

def Law3041 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3042.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w) w)

def Law3042 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3043.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w) u)

def Law3043 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3044.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) x)

def Law3044 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3045.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) y)

def Law3045 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3046.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) z)

def Law3046 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3047.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) w)

def Law3047 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3048.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) u)

def Law3048 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3049.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u) v)

def Law3049 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation3050.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x) x)

def Law3050 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3051.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x) y)

def Law3051 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3052.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y) x)

def Law3052 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3053.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y) y)

def Law3053 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3054.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) y) z)

def Law3054 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3055.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x) x)

def Law3055 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3056.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x) y)

def Law3056 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3057.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) x) z)

def Law3057 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3058.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y) x)

def Law3058 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3059.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y) y)

def Law3059 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3060.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) y) z)

def Law3060 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3061.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z) x)

def Law3061 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3062.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z) y)

def Law3062 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3063.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z) z)

def Law3063 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3064.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y) z) w)

def Law3064 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3065.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x) x)

def Law3065 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3066.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x) y)

def Law3066 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3067.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) x) z)

def Law3067 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3068.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y) x)

def Law3068 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3069.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y) y)

def Law3069 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3070.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) y) z)

def Law3070 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3071.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z) x)

def Law3071 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3072.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z) y)

def Law3072 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3073.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z) z)

def Law3073 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3074.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x) z) w)

def Law3074 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3075.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x) x)

def Law3075 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3076.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x) y)

def Law3076 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3077.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) x) z)

def Law3077 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3078.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y) x)

def Law3078 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3079.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y) y)

def Law3079 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3080.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) y) z)

def Law3080 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3081.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z) x)

def Law3081 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3082.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z) y)

def Law3082 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3083.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z) z)

def Law3083 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3084.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y) z) w)

def Law3084 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3085.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x) x)

def Law3085 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3086.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x) y)

def Law3086 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3087.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x) z)

def Law3087 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3088.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) x) w)

def Law3088 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3089.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y) x)

def Law3089 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3090.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y) y)

def Law3090 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3091.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y) z)

def Law3091 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3092.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) y) w)

def Law3092 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3093.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z) x)

def Law3093 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3094.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z) y)

def Law3094 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3095.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z) z)

def Law3095 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3096.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) z) w)

def Law3096 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3097.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w) x)

def Law3097 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3098.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w) y)

def Law3098 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3099.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w) z)

def Law3099 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3100.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w) w)

def Law3100 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3101.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z) w) u)

def Law3101 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3102.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x) x)

def Law3102 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3103.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x) y)

def Law3103 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3104.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) x) z)

def Law3104 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3105.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y) x)

def Law3105 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3106.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y) y)

def Law3106 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3107.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) y) z)

def Law3107 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3108.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z) x)

def Law3108 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3109.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z) y)

def Law3109 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3110.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z) z)

def Law3110 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3111.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x) z) w)

def Law3111 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3112.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x) x)

def Law3112 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3113.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x) y)

def Law3113 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3114.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) x) z)

def Law3114 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3115.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y) x)

def Law3115 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3116.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y) y)

def Law3116 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3117.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) y) z)

def Law3117 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3118.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z) x)

def Law3118 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3119.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z) y)

def Law3119 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3120.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z) z)

def Law3120 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3121.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y) z) w)

def Law3121 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3122.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x) x)

def Law3122 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3123.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x) y)

def Law3123 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3124.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x) z)

def Law3124 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3125.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) x) w)

def Law3125 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3126.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y) x)

def Law3126 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3127.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y) y)

def Law3127 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3128.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y) z)

def Law3128 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3129.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) y) w)

def Law3129 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3130.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z) x)

def Law3130 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3131.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z) y)

def Law3131 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3132.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z) z)

def Law3132 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3133.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) z) w)

def Law3133 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3134.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w) x)

def Law3134 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3135.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w) y)

def Law3135 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3136.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w) z)

def Law3136 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3137.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w) w)

def Law3137 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3138.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z) w) u)

def Law3138 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3139.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x) x)

def Law3139 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3140.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x) y)

def Law3140 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3141.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) x) z)

def Law3141 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3142.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y) x)

def Law3142 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3143.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y) y)

def Law3143 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3144.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) y) z)

def Law3144 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3145.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z) x)

def Law3145 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3146.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z) y)

def Law3146 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3147.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z) z)

def Law3147 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3148.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x) z) w)

def Law3148 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3149.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x) x)

def Law3149 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3150.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x) y)

def Law3150 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3151.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) x) z)

def Law3151 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3152.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y) x)

def Law3152 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3153.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y) y)

def Law3153 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3154.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) y) z)

def Law3154 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3155.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z) x)

def Law3155 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3156.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z) y)

def Law3156 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3157.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z) z)

def Law3157 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3158.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y) z) w)

def Law3158 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3159.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x) x)

def Law3159 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3160.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x) y)

def Law3160 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3161.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x) z)

def Law3161 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3162.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) x) w)

def Law3162 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3163.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y) x)

def Law3163 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3164.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y) y)

def Law3164 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3165.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y) z)

def Law3165 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3166.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) y) w)

def Law3166 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3167.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z) x)

def Law3167 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3168.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z) y)

def Law3168 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3169.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z) z)

def Law3169 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3170.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) z) w)

def Law3170 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3171.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w) x)

def Law3171 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3172.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w) y)

def Law3172 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3173.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w) z)

def Law3173 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3174.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w) w)

def Law3174 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3175.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z) w) u)

def Law3175 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3176.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x) x)

def Law3176 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3177.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x) y)

def Law3177 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3178.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x) z)

def Law3178 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3179.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) x) w)

def Law3179 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3180.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y) x)

def Law3180 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3181.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y) y)

def Law3181 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3182.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y) z)

def Law3182 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3183.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) y) w)

def Law3183 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3184.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z) x)

def Law3184 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3185.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z) y)

def Law3185 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3186.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z) z)

def Law3186 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3187.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) z) w)

def Law3187 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3188.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w) x)

def Law3188 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3189.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w) y)

def Law3189 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3190.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w) z)

def Law3190 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3191.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w) w)

def Law3191 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3192.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) w) u)

def Law3192 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3193.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x) x)

def Law3193 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3194.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x) y)

def Law3194 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3195.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x) z)

def Law3195 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3196.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) x) w)

def Law3196 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3197.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y) x)

def Law3197 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3198.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y) y)

def Law3198 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3199.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y) z)

def Law3199 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3200.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) y) w)

def Law3200 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3201.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z) x)

def Law3201 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3202.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z) y)

def Law3202 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3203.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z) z)

def Law3203 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3204.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) z) w)

def Law3204 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3205.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w) x)

def Law3205 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3206.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w) y)

def Law3206 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3207.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w) z)

def Law3207 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3208.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w) w)

def Law3208 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3209.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y) w) u)

def Law3209 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3210.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x) x)

def Law3210 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3211.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x) y)

def Law3211 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3212.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x) z)

def Law3212 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3213.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) x) w)

def Law3213 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3214.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y) x)

def Law3214 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3215.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y) y)

def Law3215 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3216.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y) z)

def Law3216 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3217.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) y) w)

def Law3217 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3218.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z) x)

def Law3218 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3219.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z) y)

def Law3219 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3220.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z) z)

def Law3220 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3221.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) z) w)

def Law3221 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3222.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w) x)

def Law3222 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3223.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w) y)

def Law3223 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3224.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w) z)

def Law3224 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3225.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w) w)

def Law3225 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3226.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z) w) u)

def Law3226 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3227.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x) x)

def Law3227 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3228.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x) y)

def Law3228 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3229.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x) z)

def Law3229 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3230.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x) w)

def Law3230 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3231.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) x) u)

def Law3231 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3232.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y) x)

def Law3232 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3233.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y) y)

def Law3233 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3234.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y) z)

def Law3234 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3235.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y) w)

def Law3235 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3236.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) y) u)

def Law3236 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3237.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z) x)

def Law3237 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3238.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z) y)

def Law3238 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3239.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z) z)

def Law3239 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3240.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z) w)

def Law3240 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3241.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) z) u)

def Law3241 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3242.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w) x)

def Law3242 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3243.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w) y)

def Law3243 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3244.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w) z)

def Law3244 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3245.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w) w)

def Law3245 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3246.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) w) u)

def Law3246 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3247.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) x)

def Law3247 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3248.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) y)

def Law3248 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3249.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) z)

def Law3249 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3250.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) w)

def Law3250 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3251.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) u)

def Law3251 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3252.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w) u) v)

def Law3252 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))

abbrev Equation3253.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law3253 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3254.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law3254 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3255.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law3255 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3256.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law3256 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3257.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law3257 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3258.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law3258 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3259.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law3259 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3260.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law3260 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3261.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law3261 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3262.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law3262 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3263.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law3263 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3264.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law3264 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3265.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law3265 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3266.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law3266 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3267.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law3267 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3268.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law3268 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3269.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law3269 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3270.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law3270 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3271.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law3271 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3272.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law3272 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3273.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law3273 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3274.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law3274 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3275.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law3275 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3276.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law3276 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3277.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law3277 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3278.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law3278 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3279.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law3279 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3280.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law3280 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3281.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law3281 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3282.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law3282 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3283.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law3283 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3284.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law3284 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3285.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law3285 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3286.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law3286 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3287.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law3287 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3288.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law3288 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3289.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law3289 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3290.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law3290 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3291.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law3291 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3292.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law3292 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3293.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law3293 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3294.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law3294 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3295.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law3295 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3296.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law3296 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3297.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law3297 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3298.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law3298 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3299.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law3299 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3300.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law3300 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3301.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law3301 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3302.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law3302 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3303.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law3303 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3304.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law3304 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3305.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law3305 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3306.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law3306 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3307.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law3307 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3308.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law3308 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3309.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law3309 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3310.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law3310 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3311.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law3311 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3312.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law3312 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3313.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law3313 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3314.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law3314 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3315.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law3315 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3316.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law3316 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3317.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law3317 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3318.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law3318 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3319.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law3319 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3320.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law3320 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3321.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law3321 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3322.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law3322 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3323.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law3323 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3324.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law3324 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3325.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law3325 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3326.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law3326 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3327.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law3327 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3328.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law3328 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3329.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law3329 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3330.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law3330 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3331.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law3331 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3332.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law3332 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3333.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law3333 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3334.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law3334 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3335.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law3335 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3336.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law3336 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3337.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law3337 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3338.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law3338 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3339.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law3339 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3340.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law3340 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3341.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law3341 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3342.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law3342 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3343.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law3343 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3344.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law3344 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3345.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law3345 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3346.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law3346 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3347.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law3347 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3348.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law3348 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3349.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law3349 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3350.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law3350 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3351.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law3351 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3352.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law3352 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3353.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law3353 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3354.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law3354 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3355.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law3355 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3356.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law3356 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3357.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law3357 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3358.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law3358 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3359.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law3359 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3360.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law3360 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3361.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law3361 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3362.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law3362 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3363.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law3363 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3364.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law3364 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3365.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law3365 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3366.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law3366 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3367.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law3367 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3368.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law3368 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3369.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law3369 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3370.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law3370 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3371.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law3371 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3372.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law3372 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3373.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law3373 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3374.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law3374 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3375.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law3375 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3376.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law3376 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3377.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law3377 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3378.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law3378 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3379.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law3379 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3380.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)))

def Law3380 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3381.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)))

def Law3381 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3382.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x w)))

def Law3382 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3383.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law3383 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3384.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)))

def Law3384 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3385.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)))

def Law3385 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3386.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y w)))

def Law3386 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3387.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)))

def Law3387 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3388.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law3388 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3389.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)))

def Law3389 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3390.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)))

def Law3390 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3391.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w x)))

def Law3391 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3392.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w y)))

def Law3392 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3393.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w z)))

def Law3393 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3394.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w w)))

def Law3394 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3395.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x (@Magma.op.{u} G inst w u)))

def Law3395 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3396.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)))

def Law3396 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3397.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)))

def Law3397 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3398.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law3398 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3399.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x w)))

def Law3399 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3400.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law3400 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3401.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)))

def Law3401 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3402.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)))

def Law3402 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3403.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y w)))

def Law3403 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3404.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)))

def Law3404 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3405.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)))

def Law3405 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3406.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)))

def Law3406 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3407.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)))

def Law3407 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3408.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w x)))

def Law3408 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3409.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w y)))

def Law3409 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3410.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w z)))

def Law3410 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3411.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w w)))

def Law3411 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3412.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y (@Magma.op.{u} G inst w u)))

def Law3412 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3413.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)))

def Law3413 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3414.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)))

def Law3414 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3415.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)))

def Law3415 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3416.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x w)))

def Law3416 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3417.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y x)))

def Law3417 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3418.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y y)))

def Law3418 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3419.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y z)))

def Law3419 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3420.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst y w)))

def Law3420 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3421.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z x)))

def Law3421 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3422.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z y)))

def Law3422 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3423.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z z)))

def Law3423 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3424.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z w)))

def Law3424 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3425.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w x)))

def Law3425 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3426.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w y)))

def Law3426 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3427.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w z)))

def Law3427 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3428.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w w)))

def Law3428 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3429.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w u)))

def Law3429 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3430.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x x)))

def Law3430 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3431.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x y)))

def Law3431 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3432.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x z)))

def Law3432 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3433.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x w)))

def Law3433 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3434.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst x u)))

def Law3434 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3435.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y x)))

def Law3435 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3436.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y y)))

def Law3436 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3437.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y z)))

def Law3437 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3438.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y w)))

def Law3438 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3439.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst y u)))

def Law3439 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3440.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z x)))

def Law3440 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3441.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z y)))

def Law3441 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3442.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z z)))

def Law3442 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3443.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z w)))

def Law3443 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3444.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst z u)))

def Law3444 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3445.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w x)))

def Law3445 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3446.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w y)))

def Law3446 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3447.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w z)))

def Law3447 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3448.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w w)))

def Law3448 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3449.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst w u)))

def Law3449 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3450.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u x)))

def Law3450 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation3451.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u y)))

def Law3451 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation3452.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u z)))

def Law3452 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation3453.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u w)))

def Law3453 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))

abbrev Equation3454.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u u)))

def Law3454 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))

abbrev Equation3455.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst w (@Magma.op.{u} G inst u v)))

def Law3455 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))

abbrev Equation3456.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law3456 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3457.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law3457 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3458.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law3458 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3459.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law3459 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3460.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law3460 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3461.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law3461 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3462.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law3462 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3463.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law3463 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3464.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law3464 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3465.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law3465 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3466.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law3466 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3467.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law3467 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3468.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law3468 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3469.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law3469 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3470.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law3470 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3471.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law3471 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3472.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law3472 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3473.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law3473 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3474.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law3474 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3475.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law3475 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3476.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law3476 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3477.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law3477 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3478.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law3478 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3479.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law3479 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3480.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law3480 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3481.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law3481 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3482.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law3482 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3483.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law3483 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3484.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law3484 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3485.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law3485 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3486.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law3486 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3487.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law3487 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3488.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law3488 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3489.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law3489 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3490.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law3490 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3491.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law3491 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3492.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law3492 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3493.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law3493 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3494.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law3494 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3495.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law3495 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3496.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law3496 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3497.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law3497 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3498.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law3498 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3499.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law3499 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3500.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law3500 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3501.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law3501 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3502.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law3502 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3503.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law3503 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3504.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law3504 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3505.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law3505 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3506.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law3506 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3507.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law3507 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3508.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law3508 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3509.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law3509 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3510.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law3510 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3511.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law3511 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3512.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law3512 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3513.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law3513 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3514.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law3514 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3515.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law3515 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3516.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law3516 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3517.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law3517 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3518.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law3518 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3519.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law3519 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3520.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law3520 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3521.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law3521 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3522.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law3522 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3523.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law3523 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3524.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law3524 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3525.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law3525 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3526.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law3526 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3527.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law3527 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3528.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law3528 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3529.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law3529 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3530.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law3530 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3531.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law3531 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3532.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law3532 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3533.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law3533 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3534.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law3534 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3535.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law3535 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3536.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law3536 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3537.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law3537 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3538.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law3538 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3539.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law3539 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3540.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law3540 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3541.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law3541 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3542.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law3542 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3543.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law3543 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3544.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law3544 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3545.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law3545 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3546.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law3546 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3547.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law3547 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3548.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law3548 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3549.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law3549 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3550.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law3550 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3551.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law3551 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3552.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law3552 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3553.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law3553 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3554.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law3554 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3555.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law3555 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3556.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law3556 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3557.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law3557 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3558.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law3558 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3559.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law3559 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3560.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law3560 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3561.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law3561 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3562.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law3562 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3563.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law3563 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3564.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law3564 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3565.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law3565 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3566.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law3566 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3567.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law3567 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3568.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law3568 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3569.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law3569 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3570.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law3570 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3571.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law3571 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3572.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law3572 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3573.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law3573 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3574.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law3574 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3575.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law3575 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3576.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law3576 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3577.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law3577 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3578.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law3578 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3579.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law3579 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3580.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law3580 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3581.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law3581 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3582.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x))

def Law3582 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3583.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) y))

def Law3583 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3584.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) z))

def Law3584 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3585.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) w))

def Law3585 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3586.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) x))

def Law3586 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3587.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) y))

def Law3587 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3589.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) w))

def Law3589 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3590.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) x))

def Law3590 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3591.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y))

def Law3591 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3592.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law3592 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3593.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) w))

def Law3593 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3594.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) x))

def Law3594 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3595.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) y))

def Law3595 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3596.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) z))

def Law3596 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3597.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) w))

def Law3597 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3598.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) u))

def Law3598 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3599.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) x))

def Law3599 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3600.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y))

def Law3600 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3601.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) z))

def Law3601 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3602.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) w))

def Law3602 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3603.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x))

def Law3603 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3604.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) y))

def Law3604 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3605.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law3605 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3606.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) w))

def Law3606 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3607.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x))

def Law3607 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3608.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law3608 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3609.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) z))

def Law3609 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3610.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) w))

def Law3610 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3611.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) x))

def Law3611 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3612.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) y))

def Law3612 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3613.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) z))

def Law3613 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3614.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) w))

def Law3614 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3615.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst y w) u))

def Law3615 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3616.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law3616 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3617.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) y))

def Law3617 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3618.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) z))

def Law3618 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3619.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) w))

def Law3619 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3620.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) x))

def Law3620 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3621.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) y))

def Law3621 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3622.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) z))

def Law3622 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3623.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) w))

def Law3623 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3624.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) x))

def Law3624 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3625.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) y))

def Law3625 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3626.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) z))

def Law3626 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3627.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) w))

def Law3627 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3628.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) x))

def Law3628 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3629.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) y))

def Law3629 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3630.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) z))

def Law3630 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3631.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) w))

def Law3631 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3632.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) u))

def Law3632 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3633.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) x))

def Law3633 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3634.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) y))

def Law3634 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3635.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) z))

def Law3635 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3636.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) w))

def Law3636 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3637.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w x) u))

def Law3637 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3638.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) x))

def Law3638 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3639.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) y))

def Law3639 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3640.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) z))

def Law3640 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3641.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) w))

def Law3641 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3642.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) u))

def Law3642 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3643.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) x))

def Law3643 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3644.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) y))

def Law3644 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3645.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) z))

def Law3645 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3646.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) w))

def Law3646 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3647.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w z) u))

def Law3647 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3648.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) x))

def Law3648 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3649.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) y))

def Law3649 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3650.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) z))

def Law3650 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3651.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) w))

def Law3651 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3652.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w w) u))

def Law3652 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3653.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) x))

def Law3653 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3654.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) y))

def Law3654 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3655.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) z))

def Law3655 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3656.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) w))

def Law3656 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3657.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) u))

def Law3657 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3658.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) v))

def Law3658 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation3659.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x x))

def Law3659 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3660.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y))

def Law3660 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3661.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x))

def Law3661 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3662.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y))

def Law3662 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3663.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z))

def Law3663 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3664.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x x))

def Law3664 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3665.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x y))

def Law3665 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3666.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z))

def Law3666 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3667.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x))

def Law3667 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3668.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y y))

def Law3668 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3669.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z))

def Law3669 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3670.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x))

def Law3670 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3671.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y))

def Law3671 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3672.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z))

def Law3672 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3673.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w))

def Law3673 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3674.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x x))

def Law3674 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3675.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x y))

def Law3675 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3676.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z))

def Law3676 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3677.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y x))

def Law3677 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3678.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y y))

def Law3678 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3679.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z))

def Law3679 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3680.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x))

def Law3680 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3681.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y))

def Law3681 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3682.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z))

def Law3682 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3683.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w))

def Law3683 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3684.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x x))

def Law3684 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3685.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x y))

def Law3685 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3686.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z))

def Law3686 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3687.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y x))

def Law3687 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3688.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y y))

def Law3688 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3689.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z))

def Law3689 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3690.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x))

def Law3690 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3691.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y))

def Law3691 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3692.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z))

def Law3692 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3693.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w))

def Law3693 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3694.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x))

def Law3694 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3695.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y))

def Law3695 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3696.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z))

def Law3696 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3697.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w))

def Law3697 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3698.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x))

def Law3698 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3699.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y))

def Law3699 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3700.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z))

def Law3700 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3701.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w))

def Law3701 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3702.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x))

def Law3702 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3703.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y))

def Law3703 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3704.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z))

def Law3704 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3705.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w))

def Law3705 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3706.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x))

def Law3706 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3707.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y))

def Law3707 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3708.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z))

def Law3708 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3709.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w))

def Law3709 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3710.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u))

def Law3710 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3711.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x x))

def Law3711 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3712.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y))

def Law3712 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3713.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x z))

def Law3713 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3714.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x))

def Law3714 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3715.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y))

def Law3715 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3716.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z))

def Law3716 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3717.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst z x))

def Law3717 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3718.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst z y))

def Law3718 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3719.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst z z))

def Law3719 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3720.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst z w))

def Law3720 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3721.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x x))

def Law3721 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3723.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z))

def Law3723 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3724.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x))

def Law3724 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3725.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y y))

def Law3725 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3726.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y z))

def Law3726 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3727.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z x))

def Law3727 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3728.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y))

def Law3728 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3729.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z z))

def Law3729 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3730.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w))

def Law3730 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3731.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst x x))

def Law3731 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3732.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst x y))

def Law3732 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3733.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst x z))

def Law3733 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3734.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst x w))

def Law3734 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3735.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst y x))

def Law3735 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3736.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst y y))

def Law3736 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3737.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst y z))

def Law3737 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3738.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst y w))

def Law3738 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3739.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst z x))

def Law3739 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3740.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst z y))

def Law3740 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3741.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst z z))

def Law3741 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3742.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst z w))

def Law3742 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3743.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst w x))

def Law3743 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3745.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst w z))

def Law3745 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3746.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst w w))

def Law3746 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3747.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst w u))

def Law3747 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3748.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x x))

def Law3748 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3749.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x y))

def Law3749 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3750.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z))

def Law3750 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3751.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y x))

def Law3751 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3752.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y y))

def Law3752 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3753.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y z))

def Law3753 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3754.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z x))

def Law3754 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3755.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z y))

def Law3755 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3756.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z z))

def Law3756 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3757.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst z w))

def Law3757 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3758.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x x))

def Law3758 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3759.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x y))

def Law3759 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3760.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst x z))

def Law3760 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3761.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y x))

def Law3761 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3762.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y y))

def Law3762 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3763.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst y z))

def Law3763 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3764.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z x))

def Law3764 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3765.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z y))

def Law3765 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3766.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z z))

def Law3766 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3767.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) (@Magma.op.{u} G inst z w))

def Law3767 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3768.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x x))

def Law3768 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3769.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x y))

def Law3769 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3770.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x z))

def Law3770 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3771.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst x w))

def Law3771 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3772.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y x))

def Law3772 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3773.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y y))

def Law3773 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3774.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y z))

def Law3774 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3775.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y w))

def Law3775 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3776.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z x))

def Law3776 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3777.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z y))

def Law3777 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3778.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z z))

def Law3778 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3779.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst z w))

def Law3779 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3780.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w x))

def Law3780 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3781.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w y))

def Law3781 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3782.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w z))

def Law3782 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3783.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w w))

def Law3783 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3784.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst w u))

def Law3784 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3785.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst x x))

def Law3785 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3786.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst x y))

def Law3786 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3787.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst x z))

def Law3787 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3788.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst x w))

def Law3788 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3789.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst y x))

def Law3789 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3790.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst y y))

def Law3790 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3791.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst y z))

def Law3791 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3792.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst y w))

def Law3792 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3793.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst z x))

def Law3793 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3794.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst z y))

def Law3794 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3795.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst z z))

def Law3795 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3796.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst z w))

def Law3796 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3797.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst w x))

def Law3797 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3798.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst w y))

def Law3798 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3799.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst w z))

def Law3799 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3800.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst w w))

def Law3800 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3801.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst w u))

def Law3801 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3802.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst x x))

def Law3802 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3803.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst x y))

def Law3803 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3804.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst x z))

def Law3804 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3805.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst x w))

def Law3805 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3806.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst y x))

def Law3806 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3807.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst y y))

def Law3807 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3808.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst y z))

def Law3808 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3809.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst y w))

def Law3809 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3810.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst z x))

def Law3810 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3811.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst z y))

def Law3811 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3812.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst z z))

def Law3812 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3813.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst z w))

def Law3813 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3814.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst w x))

def Law3814 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3815.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst w y))

def Law3815 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3816.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst w z))

def Law3816 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3817.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst w w))

def Law3817 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3818.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z y) (@Magma.op.{u} G inst w u))

def Law3818 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3819.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst x x))

def Law3819 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3820.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst x y))

def Law3820 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3821.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst x z))

def Law3821 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3822.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst x w))

def Law3822 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3823.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst y x))

def Law3823 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3824.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst y y))

def Law3824 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3825.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst y z))

def Law3825 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3826.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst y w))

def Law3826 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3827.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst z x))

def Law3827 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3828.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst z y))

def Law3828 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3829.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst z z))

def Law3829 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3830.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst z w))

def Law3830 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3831.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst w x))

def Law3831 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3832.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst w y))

def Law3832 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3833.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst w z))

def Law3833 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3834.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst w w))

def Law3834 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3835.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z z) (@Magma.op.{u} G inst w u))

def Law3835 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3836.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst x x))

def Law3836 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3837.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst x y))

def Law3837 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3838.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst x z))

def Law3838 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3839.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst x w))

def Law3839 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3840.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst x u))

def Law3840 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3841.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y x))

def Law3841 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3842.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y y))

def Law3842 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3843.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y z))

def Law3843 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3844.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y w))

def Law3844 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3845.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst y u))

def Law3845 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3846.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z x))

def Law3846 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3847.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z y))

def Law3847 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3848.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z z))

def Law3848 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3849.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z w))

def Law3849 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3850.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst z u))

def Law3850 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3851.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w x))

def Law3851 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3852.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w y))

def Law3852 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3853.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w z))

def Law3853 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3854.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w w))

def Law3854 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3855.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst w u))

def Law3855 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3856.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u x))

def Law3856 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation3857.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u y))

def Law3857 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3858.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u z))

def Law3858 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3859.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u w))

def Law3859 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))

abbrev Equation3860.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u u))

def Law3860 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))

abbrev Equation3861.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z w) (@Magma.op.{u} G inst u v))

def Law3861 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))

abbrev Equation3863.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y)

def Law3863 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3864.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x)

def Law3864 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3865.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y)

def Law3865 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3866.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z)

def Law3866 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3867.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x)

def Law3867 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3868.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y)

def Law3868 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3869.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z)

def Law3869 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3870.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x)

def Law3870 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3871.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y)

def Law3871 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3872.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z)

def Law3872 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3873.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x)

def Law3873 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3874.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y)

def Law3874 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3875.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z)

def Law3875 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3876.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w)

def Law3876 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3877.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x)

def Law3877 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3878.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y)

def Law3878 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3879.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z)

def Law3879 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3880.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x)

def Law3880 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3881.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y)

def Law3881 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3882.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z)

def Law3882 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3883.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x)

def Law3883 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3884.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y)

def Law3884 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3885.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z)

def Law3885 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3886.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w)

def Law3886 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3887.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x)

def Law3887 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3888.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y)

def Law3888 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3889.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z)

def Law3889 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3890.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x)

def Law3890 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3891.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y)

def Law3891 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3892.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z)

def Law3892 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3893.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x)

def Law3893 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3894.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y)

def Law3894 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3895.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z)

def Law3895 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3896.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w)

def Law3896 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3897.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x)

def Law3897 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3898.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y)

def Law3898 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3899.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z)

def Law3899 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3900.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w)

def Law3900 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3901.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x)

def Law3901 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3902.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y)

def Law3902 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3903.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z)

def Law3903 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3904.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w)

def Law3904 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3905.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x)

def Law3905 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3906.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y)

def Law3906 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3907.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z)

def Law3907 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3908.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w)

def Law3908 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3909.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x)

def Law3909 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3910.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y)

def Law3910 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3911.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z)

def Law3911 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3912.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w)

def Law3912 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3913.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u)

def Law3913 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3914.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x)

def Law3914 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3915.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) y)

def Law3915 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3916.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) z)

def Law3916 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3917.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) x)

def Law3917 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3918.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) y)

def Law3918 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3919.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x y)) z)

def Law3919 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3920.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) x)

def Law3920 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3921.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) y)

def Law3921 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3922.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) z)

def Law3922 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3923.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x z)) w)

def Law3923 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3924.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) x)

def Law3924 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3925.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) y)

def Law3925 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3926.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)) z)

def Law3926 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3927.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) x)

def Law3927 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3928.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) y)

def Law3928 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3929.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y y)) z)

def Law3929 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3930.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) x)

def Law3930 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3931.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) y)

def Law3931 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3932.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) z)

def Law3932 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3933.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z)) w)

def Law3933 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3934.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) x)

def Law3934 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3935.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) y)

def Law3935 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3936.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) z)

def Law3936 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3937.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z x)) w)

def Law3937 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3938.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) x)

def Law3938 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3939.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) y)

def Law3939 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3940.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) z)

def Law3940 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3941.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)) w)

def Law3941 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3942.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) x)

def Law3942 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3943.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) y)

def Law3943 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3944.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) z)

def Law3944 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3945.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z z)) w)

def Law3945 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3946.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) x)

def Law3946 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3947.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) y)

def Law3947 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3948.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) z)

def Law3948 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3949.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) w)

def Law3949 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3950.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z w)) u)

def Law3950 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3951.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) x)

def Law3951 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3952.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) y)

def Law3952 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3953.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x x)) z)

def Law3953 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3954.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) x)

def Law3954 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3955.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) y)

def Law3955 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3956.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y)) z)

def Law3956 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3957.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) x)

def Law3957 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3958.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) y)

def Law3958 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3959.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) z)

def Law3959 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3960.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)) w)

def Law3960 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3961.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) x)

def Law3961 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3962.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) y)

def Law3962 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3963.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)) z)

def Law3963 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3964.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) x)

def Law3964 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3965.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) y)

def Law3965 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3966.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y y)) z)

def Law3966 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3967.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) x)

def Law3967 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3968.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) y)

def Law3968 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3969.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) z)

def Law3969 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3970.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y z)) w)

def Law3970 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3971.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) x)

def Law3971 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3972.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) y)

def Law3972 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3973.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) z)

def Law3973 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3974.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z x)) w)

def Law3974 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3975.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) x)

def Law3975 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3976.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) y)

def Law3976 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3977.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) z)

def Law3977 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3978.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z y)) w)

def Law3978 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3979.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) x)

def Law3979 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3980.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) y)

def Law3980 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3981.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) z)

def Law3981 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3982.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z z)) w)

def Law3982 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3983.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) x)

def Law3983 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3984.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) y)

def Law3984 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3985.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) z)

def Law3985 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3986.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) w)

def Law3986 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3987.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y (@Magma.op.{u} G inst z w)) u)

def Law3987 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation3988.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) x)

def Law3988 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3989.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) y)

def Law3989 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3990.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) z)

def Law3990 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3991.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x x)) w)

def Law3991 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3992.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) x)

def Law3992 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3993.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) y)

def Law3993 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3995.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) w)

def Law3995 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation3996.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) x)

def Law3996 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3997.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) y)

def Law3997 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation3998.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) z)

def Law3998 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation3999.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x z)) w)

def Law3999 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
