module



@[expose] public section

universe u v v' w

/-- Type class for "take first n elements" operations: `v⟦:m⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the stop index type `stop`, the validity predicate `valid`. -/
class SliceLT (coll : Type u) (stop : Type v) (valid : outParam (coll → stop → Prop))
    (subcoll : outParam ((xs : coll) → (stop : stop) → (h : valid xs stop) → Type w)) where
  sliceLT : (xs : coll) → (stop : stop) → (h : valid xs stop) → subcoll xs stop h

/-- Type class for "drop first n elements" operations: `v⟦m:⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the start index type `start`, the validity predicate `valid`. -/
class SliceGE (coll : Type u) (start : Type v) (valid : outParam (coll → start → Prop))
    (subcoll : outParam ((xs : coll) → (start : start) → (h : valid xs start) → Type w)) where
  sliceGE : (xs : coll) → (start : start) → (h : valid xs start) → subcoll xs start h

/-- Type class for "slice range" operations: `v⟦m₁:m₂⟧`

We allow for the final subcollection type `subcoll` to depend on all prior parameters: the
collection type `coll`, the start index type `start`, the stop index type `stop`, the
validity predicate `valid`. -/
class Slice (coll : Type u) (start : Type v) (stop : Type v')
    (valid : outParam (coll → start → stop → Prop))
    (subcoll : outParam ((xs : coll) → (start : start) → (stop : stop) →
        (h : valid xs start stop) → Type w)) where
  slice : (xs : coll) → (start : start) → (stop : stop) →
          (h : valid xs start stop) → subcoll xs start stop h

/-- Notation `v⟦:stop⟧` for taking the first `stop` elements
(indexed from `0` to `stop - 1`) of a collection, assuming the validity for `stop` can be
automatically proven -/
syntax:max (name := sliceLTNotation) term "⟦" ":" term "⟧" : term

macro_rules (kind := sliceLTNotation)
  | `($v⟦: $stop⟧) => `(SliceLT.sliceLT $v $stop (by get_elem_tactic))

/-- Notation `v⟦:stop⟧'h` for taking the first `stop` elements
(indexed from `0` to `stop - 1`) with explicit proof -/
syntax (name := sliceLTNotationWithProof) term "⟦" ":" term "⟧'" term:max : term

macro_rules (kind := sliceLTNotationWithProof)
  | `($v⟦: $stop⟧' $h) => `(SliceLT.sliceLT $v $stop $h)

/-- Notation `v⟦start:⟧` for dropping the first `start` elements of a collection, assuming the
validity for `start` can be automatically proven -/
syntax:max (name := sliceGENotation) term "⟦" term ":" "⟧" : term

macro_rules (kind := sliceGENotation)
  | `($v⟦$start :⟧) => `(SliceGE.sliceGE $v $start (by get_elem_tactic))

/-- Notation `v⟦start:⟧'h` for dropping the first `start` elements with explicit proof -/
syntax (name := sliceGENotationWithProof) term "⟦" term ":" "⟧'" term:max : term

macro_rules (kind := sliceGENotationWithProof)
  | `($v⟦$start :⟧' $h) => `(SliceGE.sliceGE $v $start $h)

/-- Notation `v⟦start:stop⟧` for taking elements from index `start` to `stop - 1`
(e.g., `v⟦1:3⟧ = v[1] ++ v[2]`), with range proofs automatically synthesized -/
syntax:max (name := sliceNotation) term "⟦" term ":" term "⟧" : term

macro_rules (kind := sliceNotation)
  | `($v⟦$start : $stop⟧) => `(Slice.slice $v $start $stop (by get_elem_tactic))

/-- Notation `v⟦start:stop⟧'h` for taking elements from index `start` to `stop - 1`
(e.g., `v⟦1:3⟧ = ![v 1, v 2]`), with explicit proof -/
syntax (name := sliceNotationWithProof)
  term "⟦" term ":" term "⟧'" term:max : term

macro_rules (kind := sliceNotationWithProof)
  | `($v⟦$start : $stop⟧' $h) => `(Slice.slice $v $start $stop $h)

instance {α : Type u} : SliceLT (Array α) Nat (fun _ _ => True) (fun _ _ _ => Array α) where
  sliceLT xs stop _ := xs.take stop

instance {α : Type u} : SliceGE (Array α) Nat (fun _ _ => True) (fun _ _ _ => Array α) where
  sliceGE xs start _ := xs.drop start

instance {α : Type u} : Slice (Array α) Nat Nat (fun _ _ _ => True) (fun _ _ _ _ => Array α) where
  slice xs start stop _ := xs.extract start stop

instance {α : Type u} : SliceLT (List α) Nat (fun _ _ => True) (fun _ _ _ => List α) where
  sliceLT xs stop _ := List.take stop xs

instance {α : Type u} : SliceGE (List α) Nat (fun _ _ => True) (fun _ _ _ => List α) where
  sliceGE xs start _ := List.drop start xs

instance {α : Type u} : Slice (List α) Nat Nat (fun _ _ _ => True) (fun _ _ _ _ => List α) where
  slice xs start stop _ := xs.extract start stop
