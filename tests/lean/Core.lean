prelude
/-!
Core-fragment test module for Lean0: axioms, definitions and theorems only.
`prelude` keeps Init (and with it every inductive type) out of the environment.
-/

universe u v w

noncomputable section

def id' {α : Sort u} (a : α) : α := a

def comp {α : Sort u} {β : Sort v} {γ : Sort w} (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

def const' {α : Sort u} {β : Sort v} (a : α) (_ : β) : α := a

def arrowTy (α : Sort u) (β : Sort v) : Sort (imax u v) := α → β

-- inferred `Sort (imax (u+1) (v+1))`, declared `Sort (max u v + 1)`: needs level reasoning
def arrowTy' (α : Type u) (β : Type v) : Type (max u v) := α → β

-- impredicative logic
def LEq {α : Sort u} (a b : α) : Prop := ∀ P : α → Prop, P a → P b
theorem LEq.refl {α : Sort u} (a : α) : LEq a a := fun _ h => h
theorem LEq.symm {α : Sort u} {a b : α} (h : LEq a b) : LEq b a :=
  h (fun x => LEq x a) (LEq.refl a)

def False' : Prop := ∀ p : Prop, p
def Not' (p : Prop) : Prop := p → False'
def And' (p q : Prop) : Prop := ∀ r : Prop, (p → q → r) → r
theorem And'.intro {p q : Prop} (a : p) (b : q) : And' p q := fun _ k => k a b
theorem and_comm' (p q : Prop) : And' p q → And' q p := fun h r k => h r (fun a b => k b a)

-- Church numerals
def CNat : Type 1 := (α : Type) → (α → α) → α → α
def zero : CNat := fun _ _ z => z
def succ (n : CNat) : CNat := fun α s z => s (n α s z)
def add (m n : CNat) : CNat := fun α s z => m α s (n α s z)
def mul (m n : CNat) : CNat := fun α s => m α (n α s)
def two : CNat := succ (succ zero)
def four : CNat := succ (succ (succ (succ zero)))

theorem two_add_two : LEq (add two two) four := LEq.refl _
theorem two_mul_two : LEq (mul two two) four := LEq.refl _

-- eta and proof irrelevance
theorem eta_ex {α : Sort u} {β : Sort v} (f : α → β) : LEq f (fun x => f x) := LEq.refl f
theorem pirr_ex (p : Prop) (h1 h2 : p) : LEq h1 h2 := LEq.refl h1

-- opaque constants at equivalent levels
axiom Inh (α : Sort u) : Prop
axiom inh_arrow {α : Sort u} {β : Sort v} : Inh β → Inh (α → β)
theorem inh_lvl {α : Sort u} {β : Sort v} (h : Inh β) : Inh (α → β) := inh_arrow h
set_option linter.checkUnivs false in
axiom Pt.{a, b} : Sort (max a b)
theorem pt_comm : LEq (Pt.{u, v} → Pt.{u, v}) (Pt.{u, v} → Pt.{u, v}) := LEq.refl _

-- constants at different but equivalent levels
set_option linter.checkUnivs false
theorem sort_comm : LEq (Sort (max u v)) (Sort (max v u)) := LEq.refl _
theorem pt_lvl : LEq Pt.{max u v, w} Pt.{max v u, w} := LEq.refl _

end
