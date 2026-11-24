/-! Pre-sets (`PSet.{0}` as in Mathlib, a copy without imports), with `Equiv` and `Mem`, and their
characterizations stated with `∀` and `→` alone (`False` as `∀ p : Prop, p`): the premises of the
model's collapse theorems (spec/tg/model-set.mm0). -/
-- lean0-export: L0.e1 L0.e2 L0.e3 L0.m1 L0.m2 L0.empty_ex
namespace L0

inductive PSet : Type 1
  | mk (α : Type) (A : α → PSet) : PSet
set_option linter.unusedVariables false

def PSet.Equiv (x y : PSet) : Prop :=
  PSet.rec (motive := fun _ => PSet → Prop)
    (fun _ A IH y => PSet.casesOn (motive := fun _ => Prop) y fun _ B =>
      (∀ a, ∃ b, IH a (B b)) ∧ (∀ b, ∃ a, IH a (B b))) x y

def PSet.Mem (x y : PSet) : Prop :=
  PSet.casesOn (motive := fun _ => Prop) y fun _ B => ∃ b, PSet.Equiv x (B b)

open PSet

-- `∃ x, p x` in the fragment: `¬ ∀ x, ¬ p x`, with `¬ q` as `q → ∀ p : Prop, p`
local macro "⊥'" : term => `(∀ p : Prop, p)

theorem ex_of {β : Type} {p : β → Prop} (h : (∀ b, p b → ⊥') → ⊥') : ∃ b, p b :=
  Classical.byContradiction fun hn => h (fun b hb => absurd ⟨b, hb⟩ hn) False

theorem e1 : ∀ (α : Type) (A : α → PSet) (β : Type) (B : β → PSet),
    Equiv (mk α A) (mk β B) → ∀ a : α, (∀ b : β, Equiv (A a) (B b) → ⊥') → ⊥' :=
  fun _ _ _ _ h a k => (And.left h a).elim fun b hb => k b hb

theorem e2 : ∀ (α : Type) (A : α → PSet) (β : Type) (B : β → PSet),
    Equiv (mk α A) (mk β B) → ∀ b : β, (∀ a : α, Equiv (A a) (B b) → ⊥') → ⊥' :=
  fun _ _ _ _ h b k => (And.right h b).elim fun a ha => k a ha

theorem e3 : ∀ (α : Type) (A : α → PSet) (β : Type) (B : β → PSet),
    (∀ a : α, (∀ b : β, Equiv (A a) (B b) → ⊥') → ⊥') →
    (∀ b : β, (∀ a : α, Equiv (A a) (B b) → ⊥') → ⊥') → Equiv (mk α A) (mk β B) :=
  fun _ _ _ _ h1 h2 => And.intro (fun a => ex_of (h1 a)) (fun b => ex_of (h2 b))

theorem m1 : ∀ (x : PSet) (β : Type) (B : β → PSet),
    Mem x (mk β B) → (∀ b : β, Equiv x (B b) → ⊥') → ⊥' :=
  fun _ _ _ h k => Exists.elim h fun b hb => k b hb

theorem m2 : ∀ (x : PSet) (β : Type) (B : β → PSet) (b : β), Equiv x (B b) → Mem x (mk β B) :=
  fun _ _ _ b h => Exists.intro b h

/-- There is an empty set: `∃ x, ∀ y, ¬ y ∈ x`. -/
theorem empty_ex : (∀ x : PSet, (∀ y : PSet, Mem y x → ⊥') → ⊥') → ⊥' :=
  fun k => k (mk Empty (fun e => nomatch e)) (fun _ h => Exists.elim h fun b _ => nomatch b)

end L0
