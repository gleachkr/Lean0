/-! Nested inductive types: certified as the kernel's mutual block with auxiliary types, the
occurrences restored in the statements (audit §4). -/
-- lean0-export: tree_size_ex two_ex rose_kids_ex rose_val_ex forest_ex ab_ex w_ex Pat.ctorElim
universe u

-- a nested occurrence whose arguments mention a parameter
inductive Tree (α : Type u) where
  | node : α → List (Tree α) → Tree α

mutual
def Tree.size : Tree α → Nat
  | .node _ ts => 1 + Tree.sizeList ts
termination_by structural t => t
def Tree.sizeList : List (Tree α) → Nat
  | [] => 0
  | t :: ts => t.size + Tree.sizeList ts
termination_by structural ts => ts
end
theorem tree_size_ex : (Tree.node 1 [Tree.node 2 [], Tree.node 3 []]).size = 3 := rfl

-- two levels of auxiliary types (`Array S`, then `List S`), as `Lean.Syntax`
inductive S where
  | leaf : Nat → S
  | node : Array S → S
theorem two_ex : S.node #[S.leaf 1] = S.node #[S.leaf 1] := rfl

-- a structure with a nested field: projections, no eta
structure Rose where
  val : Nat
  kids : List Rose
theorem rose_kids_ex : (Rose.mk 1 []).kids = [] := rfl
theorem rose_val_ex (r : Rose) : r.val = r.1 := rfl

-- an occurrence of a nested type (its constructors mention its own auxiliary type)
inductive Forest where
  | mk : Tree Forest → Forest
theorem forest_ex (t : Tree Forest) : Forest.mk t = Forest.mk t := rfl

-- a mutual block with a nested occurrence
mutual
inductive A where
  | mk : List B → A
inductive B where
  | mk : A → B
end
theorem ab_ex (b : B) : A.mk [b] = A.mk [b] := rfl

-- an occurrence of an indexed family
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
inductive W where
  | mk : Vec W 2 → W
theorem w_ex (v : Vec W 2) : W.mk v = W.mk v := rfl

-- a field whose type has a literal: its definitions are not unfolded when the constructor's
-- type is restored, and the iota step takes the field at that type
structure Tag (k : Nat) where
  n : Nat
inductive Pat where
  | one (name : Tag 0)
  | tuple (args : List Pat)
