/-! Binder annotations: the kernel consumes `outParam`, `optParam` and `autoParam` in the
binders it re-creates for recursors, and a projection's type keeps them. -/
-- lean0-export: annot_ex annot_opt annot_auto annot_eta

class Conv (α : Type) (β : outParam Type) where
  conv : α → β
  conv_self : ∀ a, conv a = conv a := by intro a; rfl

structure Pt where
  x : Nat
  y : Nat := 0

instance : Conv Nat Bool where
  conv n := n == 0

theorem annot_ex (n : Nat) : Conv.conv n = (n == 0) := rfl
theorem annot_opt (p : Pt) : p.y + 0 = p.y := Nat.add_zero p.y
theorem annot_auto (n : Nat) : Conv.conv (β := Bool) n = Conv.conv n := Conv.conv_self n
-- structure eta at a type whose parameter binder is annotated (the closed equation is
-- instantiated at the parameters, typed at the block's stripped binders)
theorem annot_eta (c : Conv Nat Bool) : c = ⟨c.conv, c.conv_self⟩ := rfl
