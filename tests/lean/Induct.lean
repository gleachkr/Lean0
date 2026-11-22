/-! Milestone 4 test module: inductive types, structures, projections and quotients.
Only the names on the `lean0-export` line (and what they depend on) are exported. -/
-- lean0-export: two_add_two len_ex proj_red prod_eta and_swap eq_symm k_ex unit_eta sigma_ex quot_ex quot_ind_ex ev_rec_ex opq_ex thm_ex opq_c_ex opq_c_lvl propext_ex quot_sound_ex choice_ex
universe u v

noncomputable section

inductive MyNat
  | zero
  | succ (n : MyNat)
inductive MyList (α : Type u)
  | nil
  | cons (head : α) (tail : MyList α)

open MyNat MyList

def MyNat.add (n m : MyNat) : MyNat := MyNat.rec n (fun _ ih => succ ih) m
theorem two_add_two : MyNat.add (succ (succ zero)) (succ (succ zero)) = succ (succ (succ (succ zero))) := rfl
def MyList.length {α : Type u} (l : MyList α) : MyNat := MyList.rec zero (fun _ _ ih => succ ih) l
theorem len_ex : MyList.length (cons zero (cons zero nil)) = succ (succ zero) := rfl
theorem proj_red {α : Type u} {β : Type v} (a : α) (b : β) : (Prod.mk a b).1 = a := rfl
theorem prod_eta {α : Type u} {β : Type v} (p : Prod α β) : p = Prod.mk p.1 p.2 := rfl
theorem and_swap {a b : Prop} (h : And a b) : And b a := And.intro h.2 h.1
theorem eq_symm {α : Sort u} {a b : α} (h : a = b) : b = a := Eq.rec (motive := fun x _ => x = a) rfl h
theorem k_ex (n : MyNat) (h : n = n) : (Eq.rec (motive := fun _ _ => MyNat) zero h) = zero := rfl
theorem unit_eta (x y : PUnit.{u}) : x = y := rfl
theorem sigma_ex {α : Type u} {β : α → Type v} (s : Sigma β) : Sigma.mk s.1 s.2 = s := rfl
theorem quot_ex {α : Sort u} {β : Sort v} (r : α → α → Prop) (f : α → β) (h : ∀ a b, r a b → f a = f b) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a := rfl

end
-- `Quot.ind` on `Quot.mk` as a recursor's major premise: the kernel reduces it to reach the
-- constructor (certified by proof irrelevance: both sides prove the same proposition)
theorem quot_ind_ex (r : Nat → Nat → Prop) (a : Nat) (p q : Prop) (hp : p) (hq : q) :
    And.rec (motive := fun _ => Nat) (fun _ _ => 5)
      (Quot.ind (β := fun _ => p ∧ q) (fun _ => And.intro hp hq) (Quot.mk r a)) = 5 := rfl
-- a mutual inductive: each recursor's rules mention the other recursor
mutual
inductive Ev : Type
  | zero : Ev
  | succ : Od → Ev
inductive Od : Type
  | succ : Ev → Od
end
theorem ev_rec_ex : Ev.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 0 (fun _ ih => ih + 1)
    (fun _ ih => ih + 1) (Ev.succ (Od.succ Ev.zero)) = 2 := rfl

-- An opaque constant at the block's level in a structure's field: the structure's lemmas need
-- the constant's level congruence (`eeqv_cst`, the constant being `cst Opq_atom ...`).
axiom Opq : Type u
structure OpqS where
  x : Opq.{u}
theorem opq_ex (s : OpqS.{u}) : s = OpqS.mk s.x := rfl

-- A theorem constant at the block's level in a field's type: the structure's lemmas need the
-- constant's level congruence, a theorem proved from its proof term where it is declared
-- (and so for the theorems its proof term mentions: `thm_u`, through the definition `thm_d`).
theorem thm_u (α : Sort u) (a : α) : a = a := rfl
def thm_d (α : Sort u) (a : α) : a = a := thm_u α a
theorem thm_v (α : Sort u) (a : α) : a = a := thm_d α a
structure ThmS (α : Sort u) (a : α) : Prop where
  h : thm_v α a = thm_v α a
theorem thm_ex (α : Sort u) (a : α) (s : ThmS α a) : s = ThmS.mk s.h := rfl

-- An opaque constant is certified like a theorem (an abstract definition by its value: its
-- type is proved, not assumed), with its level congruence when a block mentions it.
opaque opq_c (α : Type u) : Nat := 0
structure OpqC (α : Type u) where
  x : Fin (opq_c α + 1)
theorem opq_c_ex (α : Type u) (s : OpqC α) : s = OpqC.mk s.x := rfl
-- the opaque constant at equivalent levels (by its level congruence)
theorem opq_c_lvl (α : Type u) : opq_c.{max u u} α = opq_c.{u} α := rfl

-- `propext`, `Quot.sound` and `Classical.choice` are constants of the spec, typed by its rules: no axiom
theorem propext_ex (a b : Prop) (h : a ↔ b) : a = b := propext h
theorem quot_sound_ex {α : Sort u} (r : α → α → Prop) (a b : α) (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h
noncomputable def choice_ex {α : Sort u} (h : Nonempty α) : α := Classical.choice h
