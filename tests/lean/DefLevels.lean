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
-- The `imax` identities the generator proves from the spec's level rules, one each (Lean's kernel
-- does not prove the distribution over `max` or `imax` itself; the generator's normal forms use it).
def Tag2.{x, y} (p : Prop) : Prop := Tag.{imax x y} p
theorem imax_zero_l : LEq (Tag2.{0, u} False') (Tag.{u} False') := LEq.refl _
theorem imax_one : LEq (Tag.{imax 1 u} False') (Tag.{u} False') := LEq.refl _
theorem imax_self : LEq (Tag.{imax u u} False') (Tag.{u} False') := LEq.refl _
theorem imax_max : LEq (Tag.{imax u (max v w)} False') (Tag.{imax u (max w v)} False') := LEq.refl _
theorem imax_imax : LEq (Tag.{imax (max u v) (imax v w)} False') (Tag.{imax (max v u) (imax v w)} False') := LEq.refl _
end
