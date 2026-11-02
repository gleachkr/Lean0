namespace Demo

def double (n : Nat) : Nat := n + n

theorem double_comm (a b : Nat) : double a + double b = double b + double a :=
  Nat.add_comm _ _

inductive Tree where
  | leaf
  | node (l r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

theorem Tree.size_pos (t : Tree) : 0 < t.size :=
  match t with
  | .leaf => Nat.zero_lt_one
  | .node _ _ => Nat.succ_pos _

end Demo
