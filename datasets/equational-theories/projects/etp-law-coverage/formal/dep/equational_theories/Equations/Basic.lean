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

abbrev Equation1.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [Magma.{u} G] => ∀ (x : G), @Eq.{u + 1} G x x

def Law1 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

abbrev Equation2.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [Magma.{u} G] => ∀ (x y : G), @Eq.{u + 1} G x y

def Law2 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

abbrev Equation3.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst x x)

def Law3 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst x y)

def Law4 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation5.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y x)

def Law5 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation6.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y y)

def Law6 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation7.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x y z : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y z)

def Law7 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation8.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x))

def Law8 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation14.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x y))

def Law14 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation16.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x))

def Law16 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation23.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] => ∀ (x : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)

def Law23 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation29.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) y)

def Law29 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation38.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x y)

def Law38 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation39.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y x)

def Law39 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation40.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y y)

def Law40 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation41.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst y z)

def Law41 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation42.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x z)

def Law42 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation43.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst y x)

def Law43 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation45.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z y)

def Law45 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation46.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst z w)

def Law46 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation65.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x)))

def Law65 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation168.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x z))

def Law168 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation203.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G), @Eq.{u + 1} G x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x)

def Law203 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation381.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) y)

def Law381 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

abbrev Equation387.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G), @Eq.{u + 1} G (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) x)

def Law387 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation614.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x)))

def Law614 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat
        (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation817.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x x)))

def Law817 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation953.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst y (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) (@Magma.op.{u} G inst z z)))

def Law953 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1426.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)))

def Law1426 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1485.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst x (@Magma.op.{u} G inst z y)))

def Law1485 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))

abbrev Equation1491.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst y x)))

def Law1491 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))

abbrev Equation1571.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) (@Magma.op.{u} G inst y (@Magma.op.{u} G inst x z)))

def Law1571 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))

abbrev Equation1659.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y y) z))

def Law1659 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1661.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) y))

def Law1661 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation1689.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) z))

def Law1689 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation1701.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst y x) (@Magma.op.{u} G inst (@Magma.op.{u} G inst z x) x))

def Law1701 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

abbrev Equation2162.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst y z) x) (@Magma.op.{u} G inst x y))

def Law2162 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation2662.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G x
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x y)) x)

def Law2662 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3588.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst z (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z))

def Law3588 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation3722.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) (@Magma.op.{u} G inst x y))

def Law3722 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3744.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x z) (@Magma.op.{u} G inst w y))

def Law3744 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))

abbrev Equation3862.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x (@Magma.op.{u} G inst x x)) x)

def Law3862 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation3994.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x y)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst z (@Magma.op.{u} G inst x y)) z)

def Law3994 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4065.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x x)
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst (@Magma.op.{u} G inst x x) x) x)

def Law4065 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat
      (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))

abbrev Equation4315.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y x))
      (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))

def Law4315 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))

abbrev Equation4512.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) z)

def Law4512 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4513.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x y) w)

def Law4513 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))

abbrev Equation4522.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst x w) u)

def Law4522 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))

abbrev Equation4564.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w y) z)

def Law4564 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4579.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) z)

def Law4579 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))

abbrev Equation4582.{u} : (G : Type u) → [a : Magma.{u} G] → Prop :=
  fun (G : Type u) [inst : Magma.{u} G] =>
  ∀ (x y z w u v : G),
    @Eq.{u + 1} G (@Magma.op.{u} G inst x (@Magma.op.{u} G inst y z))
      (@Magma.op.{u} G inst (@Magma.op.{u} G inst w u) v)

def Law4582 : Law.NatMagmaLaw :=
  @Law.MagmaLaw.mk.{0} Nat
  (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (@FreeMagma.Fork.{0} Nat
    (@FreeMagma.Fork.{0} Nat (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@FreeMagma.Leaf.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
