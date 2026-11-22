/-! Milestone 4 test module: inductive types, structures, projections and quotients.
Only the names on the `lean0-export` line (and what they depend on) are exported. -/
-- lean0-export: two_add_two len_ex proj_red prod_eta and_swap eq_symm k_ex unit_eta sigma_ex quot_ex quot_ind_ex ev_rec_ex opq_ex
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
