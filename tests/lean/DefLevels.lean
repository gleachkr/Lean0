prelude
/-! A definition used at two different but equivalent universe levels. -/
universe u v w
set_option linter.checkUnivs false
noncomputable section
def LEq {α : Sort u} (a b : α) : Prop := ∀ P : α → Prop, P a → P b
theorem LEq.refl {α : Sort u} (a : α) : LEq a a := fun _ h => h
def False' : Prop := ∀ p : Prop, p
def Tag.{x} (p : Prop) : Prop := (Sort x → p) → p
theorem tag_lvl : LEq (Tag.{max u v} False') (Tag.{max v u} False') := LEq.refl _
end
