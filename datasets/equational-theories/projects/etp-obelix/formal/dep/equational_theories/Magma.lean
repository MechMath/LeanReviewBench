

class Magma (α : Type _) where
  /-- `a ◇ b` denotes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- This instance is (only) available after writing `open MagmaToMul` -/
scoped instance MagmaToMul.inst {α : Type _} [Magma α] : Mul α where
  mul := Magma.op

/-- This instance is (only) available after writing `open MagmaToAdd` -/
scoped instance MagmaToAdd.inst {α : Type _} [Magma α] : Add α where
  add := Magma.op

/-- This instance is (only) available after writing `open MulToMagma` -/
scoped instance MulToMagma.inst {α : Type _} [Mul α] : Magma α where
  op := (· * ·)

/-- This instance is (only) available after writing `open AddToMagma` -/
scoped instance AddToMagma.inst {α : Type _} [Add α] : Magma α where
  op := (· + ·)
