/-
The proofs lean0 carries of the equations the spec's rules for the division-like literal
operations ask for (`divmod_eqs`, `gcd_eqs`, `land_eqs`, `lor_eqs`, `xor_eqs` in
spec/lean-lit.mm0; notes/audit-lean-mm0.md §5), for Lean's definitions of `Nat.div`,
`Nat.mod`, `Nat.gcd` and `Nat.bitwise` (Lean v4.35.0). `scripts/baked.sh` exports the
theorems listed at the end to `baked.ndjson`, which lean0 embeds: where a certificate needs
one, its proof term is elaborated like any other, with the lemmas of this file inlined.

The proofs use only what the operations' own definitions depend on (and a few lemmas of
`Init.Prelude`, inlined too when an export lacks them): no `simp`, no `omega`, no `funext`.
-/
namespace Lean0
open Nat WellFounded

attribute [local semireducible] Nat.div Nat.modCore Nat.bitwise Nat.gcd

/-! ### Stand-ins

An operation's rule is about four functions (`divmod_eqs G fd fm fmul fadd`), and Lean's
definition of one does not depend on the others: `Nat.div` on neither `Nat.mod` nor
`Lean0.mul`. So that an export needs nothing beyond the operation itself, the others are
terms: `mul` below, and `Lean0.div`, `Lean0.mod`, copies of Lean's definitions (equal to
them by unfolding: `div_eq`, `mod_eq`). -/

/-- Multiplication by recursion on the second argument, as `Lean0.mul`. -/
def mul (x y : Nat) : Nat := @Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih x) y

set_option bootstrap.genMatcherCode false in
protected def div (x y : Nat) : Nat :=
  dite (LT.lt 0 y) (fun hy =>
    let rec
      go (fuel : Nat) (x : Nat) (hfuel : LT.lt x fuel) : Nat :=
      match fuel with
      | succ fuel =>
        dite (LE.le y x)
          (fun h => HAdd.hAdd (go fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h hfuel)) 1)
          (fun _ => 0)
      termination_by structural fuel
    go (succ x) x (Nat.lt_succ_self _))
    (fun _ => 0)

set_option bootstrap.genMatcherCode false in
protected def modCore (x y : Nat) : Nat :=
  dite (LT.lt 0 y)
    (fun hy =>
      let rec
        go (fuel : Nat) (x : Nat) (hfuel : LT.lt x fuel) : Nat :=
        match fuel with
        | succ fuel =>
          dite (LE.le y x)
            (fun h => go fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h hfuel))
            (fun _ => x)
        termination_by structural fuel
      go (succ x) x (Nat.lt_succ_self _))
    (fun _ => x)

set_option bootstrap.genMatcherCode false in
protected def mod : Nat → Nat → Nat
  | 0, _ => 0
  | n@(succ _), m => ite (LE.le m n) (Lean0.modCore n m) n

theorem div_eq : @Nat.div = @Lean0.div := by delta Nat.div Lean0.div Nat.div.go Lean0.div.go; rfl
theorem mod_eq : @Nat.mod = @Lean0.mod := by
  delta Nat.mod Lean0.mod Nat.modCore Lean0.modCore Nat.modCore.go Lean0.modCore.go; rfl

/-! ### Arithmetic -/

theorem zero_add (n : Nat) : Eq (Nat.add 0 n) n :=
  @Nat.rec (fun n => Eq (Nat.add 0 n) n) rfl (fun _ ih => congrArg Nat.succ ih) n

theorem succ_add (n m : Nat) : Eq (Nat.add (succ n) m) (succ (Nat.add n m)) :=
  @Nat.rec (fun m => Eq (Nat.add (succ n) m) (succ (Nat.add n m))) rfl (fun _ ih => congrArg Nat.succ ih) m

theorem add_comm (n m : Nat) : Eq (Nat.add n m) (Nat.add m n) :=
  @Nat.rec (fun m => Eq (Nat.add n m) (Nat.add m n)) (Eq.symm (zero_add n))
    (fun m ih => Eq.trans (congrArg Nat.succ ih) (Eq.symm (succ_add m n))) m

theorem add_assoc (n m k : Nat) : Eq (Nat.add (Nat.add n m) k) (Nat.add n (Nat.add m k)) :=
  @Nat.rec (fun k => Eq (Nat.add (Nat.add n m) k) (Nat.add n (Nat.add m k))) rfl (fun _ ih => congrArg Nat.succ ih) k

theorem add_right_comm (n m k : Nat) : Eq (Nat.add (Nat.add n m) k) (Nat.add (Nat.add n k) m) :=
  Eq.trans (add_assoc n m k) (Eq.trans (congrArg (Nat.add n) (add_comm m k)) (Eq.symm (add_assoc n k m)))

theorem sub_add_cancel (y : Nat) : ∀ x : Nat, LE.le y x → Eq (Nat.add (Nat.sub x y) y) x :=
  @Nat.rec (fun y => ∀ x : Nat, LE.le y x → Eq (Nat.add (Nat.sub x y) y) x) (fun _ _ => rfl)
    (fun y ih x =>
      @Nat.rec (fun x => LE.le (succ y) x → Eq (Nat.add (Nat.sub x (succ y)) (succ y)) x)
        (fun h => absurd h (Nat.not_succ_le_zero y))
        (fun x _ h =>
          show Eq (succ (Nat.add (Nat.sub (succ x) (succ y)) y)) (succ x) from
          congrArg Nat.succ (Eq.trans (congrArg (fun t => Nat.add t y) (Nat.succ_sub_succ_eq_sub x y)) (ih x (Nat.le_of_succ_le_succ h))))
        x) y


/-! ### Division and modulus, for the copies -/

theorem go_spec (y : Nat) (hy : LT.lt 0 y) (fuel : Nat) : ∀ (x : Nat) (h : LT.lt x fuel),
    Eq (Nat.add (Lean0.mul y (Lean0.div.go y hy fuel x h)) (Lean0.modCore.go y hy fuel x h)) x :=
  @Nat.rec (fun fuel => ∀ (x : Nat) (h : LT.lt x fuel),
      Eq (Nat.add (Lean0.mul y (Lean0.div.go y hy fuel x h)) (Lean0.modCore.go y hy fuel x h)) x)
    (fun x h => absurd h (Nat.not_lt_zero x))
    (fun fuel ih x h =>
      show Eq (Nat.add (Lean0.mul y (dite (LE.le y x) (fun h' => HAdd.hAdd (Lean0.div.go y hy fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h' h)) 1) (fun _ => 0)))
                (dite (LE.le y x) (fun h' => Lean0.modCore.go y hy fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h' h)) (fun _ => x))) x from
      match Nat.decLe y x with
      | .isTrue hle =>
        Eq.trans (add_right_comm _ y _)
          (Eq.trans (congrArg (fun t => Nat.add t y) (ih (Nat.sub x y) (div_rec_fuel_lemma hy hle h))) (sub_add_cancel y x hle))
      | .isFalse _ => zero_add x)
    fuel

theorem modCore_of_not_le (x y : Nat) (hn : Not (LE.le y x)) : Eq (Lean0.modCore x y) x :=
  show Eq (dite (LT.lt 0 y) (fun hy => Lean0.modCore.go y hy (succ x) x (Nat.lt_succ_self _)) (fun _ => x)) x from
  match Nat.decLt 0 y with
  | .isTrue hy =>
    show Eq (dite (LE.le y x) (fun h' => Lean0.modCore.go y hy x (HSub.hSub x y) (div_rec_fuel_lemma hy h' (Nat.lt_succ_self _))) (fun _ => x)) x from
    match Nat.decLe y x with
    | .isTrue h => absurd h hn
    | .isFalse _ => rfl
  | .isFalse _ => rfl

theorem modCore_zero (y : Nat) : Eq (Lean0.modCore 0 y) 0 :=
  show Eq (dite (LT.lt 0 y) (fun hy => Lean0.modCore.go y hy 1 0 (Nat.lt_succ_self _)) (fun _ => 0)) 0 from
  match Nat.decLt 0 y with
  | .isTrue hy =>
    show Eq (dite (LE.le y 0) (fun h' => Lean0.modCore.go y hy 0 (HSub.hSub 0 y) (div_rec_fuel_lemma hy h' (Nat.lt_succ_self _))) (fun _ => 0)) 0 from
    match Nat.decLe y 0 with
    | .isTrue h => absurd (Nat.lt_of_lt_of_le hy h) (Nat.lt_irrefl 0)
    | .isFalse _ => rfl
  | .isFalse _ => rfl

theorem mod_eq_modCore : ∀ (x y : Nat), Eq (Lean0.mod x y) (Lean0.modCore x y) :=
  @Nat.rec (fun x => ∀ y : Nat, Eq (Lean0.mod x y) (Lean0.modCore x y))
    (fun y => Eq.symm (modCore_zero y))
    (fun n _ y =>
      show Eq (ite (LE.le y (succ n)) (Lean0.modCore (succ n) y) (succ n)) (Lean0.modCore (succ n) y) from
      match Nat.decLe y (succ n) with
      | .isTrue _ => rfl
      | .isFalse hn => Eq.symm (modCore_of_not_le (succ n) y hn))

theorem div_add_modCore (x y : Nat) : Eq (Nat.add (Lean0.mul y (Lean0.div x y)) (Lean0.modCore x y)) x :=
  show Eq (Nat.add (Lean0.mul y (dite (LT.lt 0 y) (fun hy => Lean0.div.go y hy (succ x) x (Nat.lt_succ_self _)) (fun _ => 0)))
            (dite (LT.lt 0 y) (fun hy => Lean0.modCore.go y hy (succ x) x (Nat.lt_succ_self _)) (fun _ => x))) x from
  match Nat.decLt 0 y with
  | .isTrue hy => go_spec y hy (succ x) x (Nat.lt_succ_self _)
  | .isFalse _ => zero_add x

theorem c_div_add_mod (x y : Nat) : Eq (Nat.add (Lean0.mul y (Lean0.div x y)) (Lean0.mod x y)) x :=
  Eq.trans (congrArg (Nat.add (Lean0.mul y (Lean0.div x y))) (mod_eq_modCore x y)) (div_add_modCore x y)

theorem c_div_zero (x : Nat) : Eq (Lean0.div x 0) 0 := rfl


theorem lt_of_not_le (b : Nat) : ∀ a : Nat, Not (LE.le b a) → LT.lt a b :=
  @Nat.rec (fun b => ∀ a : Nat, Not (LE.le b a) → LT.lt a b)
    (fun a h => absurd (Nat.zero_le a) h)
    (fun b ih a =>
      @Nat.rec (fun a => Not (LE.le (succ b) a) → LT.lt a (succ b))
        (fun _ => Nat.zero_lt_succ b)
        (fun a _ h => Nat.succ_le_succ (ih a (fun h' => h (Nat.succ_le_succ h'))))
        a) b

theorem modCoreGo_lt (y : Nat) (hy : LT.lt 0 y) (fuel : Nat) : ∀ (x : Nat) (h : LT.lt x fuel),
    LT.lt (Lean0.modCore.go y hy fuel x h) y :=
  @Nat.rec (fun fuel => ∀ (x : Nat) (h : LT.lt x fuel), LT.lt (Lean0.modCore.go y hy fuel x h) y)
    (fun x h => absurd h (Nat.not_lt_zero x))
    (fun fuel ih x h =>
      show LT.lt (dite (LE.le y x) (fun h' => Lean0.modCore.go y hy fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h' h)) (fun _ => x)) y from
      match Nat.decLe y x with
      | .isTrue hle => ih (HSub.hSub x y) (div_rec_fuel_lemma hy hle h)
      | .isFalse hn => lt_of_not_le y x hn)
    fuel

theorem modCore_lt (x y : Nat) (hy : LT.lt 0 y) : LT.lt (Lean0.modCore x y) y :=
  show LT.lt (dite (LT.lt 0 y) (fun hy => Lean0.modCore.go y hy (succ x) x (Nat.lt_succ_self _)) (fun _ => x)) y from
  match Nat.decLt 0 y with
  | .isTrue hy' => modCoreGo_lt y hy' (succ x) x (Nat.lt_succ_self _)
  | .isFalse hn => absurd hy hn

/-- `0 < y → x % y < y`, as the spec states it (`Nat.le (succ 0) y → Nat.le (succ (x % y)) y`). -/
theorem c_mod_lt (x y : Nat) (h : Nat.le (Nat.succ 0) y) : Nat.le (Nat.succ (Lean0.mod x y)) y :=
  Eq.symm (mod_eq_modCore x y) ▸ modCore_lt x y h

/-! ### The three pairs: `Nat.div` with the copy of `Nat.mod`, the copy of `Nat.div` with
`Nat.mod`, and both of Lean's. -/

theorem d_div_add_mod (x y : Nat) : Eq (Nat.add (Lean0.mul y (Nat.div x y)) (Lean0.mod x y)) x :=
  @Eq.subst _ (fun d : Nat → Nat → Nat => Eq (Nat.add (Lean0.mul y (d x y)) (Lean0.mod x y)) x) _ _ div_eq.symm (c_div_add_mod x y)
theorem d_div_zero (x : Nat) : Eq (Nat.div x 0) 0 :=
  @Eq.subst _ (fun d : Nat → Nat → Nat => Eq (d x 0) 0) _ _ div_eq.symm (c_div_zero x)

theorem m_div_add_mod (x y : Nat) : Eq (Nat.add (Lean0.mul y (Lean0.div x y)) (Nat.mod x y)) x :=
  @Eq.subst _ (fun m : Nat → Nat → Nat => Eq (Nat.add (Lean0.mul y (Lean0.div x y)) (m x y)) x) _ _ mod_eq.symm (c_div_add_mod x y)
theorem mod_lt (x y : Nat) (h : Nat.le (Nat.succ 0) y) : Nat.le (Nat.succ (Nat.mod x y)) y :=
  @Eq.subst _ (fun m : Nat → Nat → Nat => Nat.le (Nat.succ (m x y)) y) _ _ mod_eq.symm (c_mod_lt x y h)

theorem div_add_mod (x y : Nat) : Eq (Nat.add (Lean0.mul y (Nat.div x y)) (Nat.mod x y)) x :=
  @Eq.subst _ (fun d : Nat → Nat → Nat => Eq (Nat.add (Lean0.mul y (d x y)) (Nat.mod x y)) x) _ _ div_eq.symm (m_div_add_mod x y)

/-! ### `Nat.bitwise` and `Nat.gcd`: the fixpoint without `funext` -/

theorem dite_ext {c : Prop} [inst : Decidable c] {α : Sort u} {t t' : c → α} {e e' : ¬ c → α}
    (ht : ∀ h, t h = t' h) (he : ∀ h, e h = e' h) : dite c t e = dite c t' e' :=
  match inst with
  | .isTrue h => ht h
  | .isFalse h => he h

section
variable {α : Sort u} {motive : α → Sort v} (h : α → Nat)
variable (F : (x : α) → ((y : α) → InvImage (· < ·) h y x → motive y) → motive x)
variable (Hext : ∀ x a b, (∀ y hy, a y hy = b y hy) → F x a = F x b)
include Hext

theorem go_congr (fuel₁ : Nat) : ∀ (x : α) (fuel₂ : Nat) (h₁ : h x < fuel₁) (h₂ : h x < fuel₂),
    Nat.fix.go h F fuel₁ x h₁ = Nat.fix.go h F fuel₂ x h₂ := by
  induction fuel₁ with
  | zero => intro x _ h₁; exact absurd h₁ (Nat.not_lt_zero _)
  | succ fuel₁ ih =>
    intro x fuel₂ h₁ h₂
    cases fuel₂ with
    | zero => exact absurd h₂ (Nat.not_lt_zero _)
    | succ fuel₂ => exact Hext x _ _ (fun y hy => ih y fuel₂ _ _)

theorem fix_eq (x : α) : Nat.fix h F x = F x (fun y _ => Nat.fix h F y) :=
  Eq.trans (go_congr h F Hext _ x (h x + 1) _ (Nat.lt_succ_self _))
    (Hext x _ _ (fun y _ => go_congr h F Hext _ y _ _ _))
end


theorem bitwise_unfold (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m =
      if n = 0 then (if f false true = true then m else 0)
      else if m = 0 then (if f true false = true then n else 0)
      else if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) = true
        then Nat.bitwise f (n / 2) (m / 2) + Nat.bitwise f (n / 2) (m / 2) + 1
        else Nat.bitwise f (n / 2) (m / 2) + Nat.bitwise f (n / 2) (m / 2) := by
  delta Nat.bitwise Nat.bitwise._unary
  refine (fix_eq (α := (_ : Nat) ×' Nat) _ _ ?hext ⟨n, m⟩).trans rfl
  intro x a b hab
  cases x with
  | mk n m =>
    exact dite_ext (fun _ => rfl) (fun hn => dite_ext (fun _ => rfl) (fun _ =>
      congrArg (fun r : Nat => if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) = true then r + r + 1 else r + r)
        (hab ⟨n / 2, m / 2⟩ (Nat.bitwise_rec_lemma hn))))

/-- The four cases of two numbers below 2. -/
theorem bits (P : Nat → Nat → Prop) (h00 : P 0 0) (h01 : P 0 1) (h10 : P 1 0) (h11 : P 1 1) :
    ∀ a b : Nat, LT.lt a 2 → LT.lt b 2 → P a b
  | 0, 0, _, _ => h00
  | 0, 1, _, _ => h01
  | 1, 0, _, _ => h10
  | 1, 1, _, _ => h11
  | a + 2, _, h, _ => absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)) (Nat.not_succ_le_zero a)
  | _, b + 2, _, h => absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)) (Nat.not_succ_le_zero b)

theorem bit (P : Nat → Prop) (h0 : P 0) (h1 : P 1) (a : Nat) (h : LT.lt a 2) : P a :=
  bits (fun a _ => P a) h0 h0 h1 h1 a 0 h (Nat.succ_le_succ (Nat.zero_le 1))

theorem two_pos : Nat.le (Nat.succ 0) 2 := Nat.succ_le_succ (Nat.zero_le 1)

theorem land_zero_left (m : Nat) : Nat.land 0 m = 0 :=
  Eq.trans (bitwise_unfold and 0 m) rfl

theorem land_zero_right : ∀ n : Nat, Nat.land n 0 = 0
  | 0 => Eq.trans (bitwise_unfold and 0 0) rfl
  | n + 1 => Eq.trans (bitwise_unfold and (n + 1) 0) rfl

theorem land_bit (r a b : Nat) (ha : LT.lt a 2) (hb : LT.lt b 2) :
    (if (decide (a = 1) && decide (b = 1)) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.div (Nat.add a b) 2) :=
  bits (fun a b => (if (decide (a = 1) && decide (b = 1)) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.div (Nat.add a b) 2))
    rfl rfl rfl rfl a b ha hb

theorem land_rec (x y : Nat) :
    Nat.land x y = Nat.add (Nat.add (Nat.land (Nat.div x 2) (Nat.div y 2)) (Nat.land (Nat.div x 2) (Nat.div y 2)))
      (Nat.div (Nat.add (Nat.mod x 2) (Nat.mod y 2)) 2) := by
  have hb : LT.lt (Nat.mod y 2) 2 := mod_lt y 2 two_pos
  have ha : LT.lt (Nat.mod x 2) 2 := mod_lt x 2 two_pos
  refine Eq.trans (bitwise_unfold and x y) ?_
  cases x with
  | zero =>
    show 0 = Nat.add (Nat.add (Nat.land 0 (Nat.div y 2)) (Nat.land 0 (Nat.div y 2))) (Nat.div (Nat.add 0 (y % 2)) 2)
    rw [land_zero_left]
    exact bit (fun b => 0 = Nat.add (Nat.add 0 0) (Nat.div (Nat.add 0 b) 2)) rfl rfl _ hb
  | succ x =>
    cases y with
    | zero =>
      show 0 = Nat.add (Nat.add (Nat.land (Nat.div (x+1) 2) 0) (Nat.land (Nat.div (x+1) 2) 0)) (Nat.div (Nat.add ((x+1) % 2) 0) 2)
      rw [land_zero_right]
      exact bit (fun a => 0 = Nat.add (Nat.add 0 0) (Nat.div (Nat.add a 0) 2)) rfl rfl _ ha
    | succ y => exact land_bit _ _ _ ha hb


theorem gcd_unfold (m n : Nat) : Nat.gcd m n = if m = 0 then n else Nat.gcd (n % m) m := by
  delta Nat.gcd Nat.gcd._unary
  refine (fix_eq (α := (_ : Nat) ×' Nat) _ _ ?hext ⟨m, n⟩).trans rfl
  intro x a b hab
  cases x with
  | mk m n => exact dite_ext (fun _ => rfl) (fun _ => hab _ _)

theorem gcd_zero (y : Nat) : Nat.gcd 0 y = y := Eq.trans (gcd_unfold 0 y) rfl
theorem gcd_succ (x y : Nat) : Nat.gcd (Nat.succ x) y = Nat.gcd (Nat.mod y (Nat.succ x)) (Nat.succ x) :=
  Eq.trans (gcd_unfold (Nat.succ x) y) rfl

theorem lor_bit (r a b : Nat) (ha : LT.lt a 2) (hb : LT.lt b 2) :
    (if (decide (a = 1) || decide (b = 1)) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.div (Nat.add (Nat.add a b) 1) 2) :=
  bits (fun a b => (if (decide (a = 1) || decide (b = 1)) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.div (Nat.add (Nat.add a b) 1) 2))
    rfl rfl rfl rfl a b ha hb

theorem two_mul (q : Nat) : Lean0.mul 2 q = Nat.add q q :=
  @Nat.rec (fun q => Lean0.mul 2 q = Nat.add q q) rfl
    (fun q ih => show Nat.succ (Nat.succ (Lean0.mul 2 q)) = Nat.succ (Nat.add (Nat.succ q) q) from
      congrArg Nat.succ (Eq.trans (congrArg Nat.succ ih) (succ_add q q).symm)) q

/-- `y = y/2 + y/2 + y%2`. -/
theorem half (y : Nat) : Nat.add (Nat.add (Nat.div y 2) (Nat.div y 2)) (Nat.mod y 2) = y :=
  Eq.trans (congrArg (fun t => Nat.add t (Nat.mod y 2)) (two_mul (Nat.div y 2)).symm) (div_add_mod y 2)

theorem bit_or0 (b : Nat) (hb : LT.lt b 2) : Nat.div (Nat.add (Nat.add 0 b) 1) 2 = b :=
  bit (fun b => Nat.div (Nat.add (Nat.add 0 b) 1) 2 = b) rfl rfl b hb

theorem bit_or0' (a : Nat) (ha : LT.lt a 2) : Nat.div (Nat.add (Nat.add a 0) 1) 2 = a :=
  bit (fun a => Nat.div (Nat.add (Nat.add a 0) 1) 2 = a) rfl rfl a ha

theorem lor_zero_left (m : Nat) : Nat.lor 0 m = m := Eq.trans (bitwise_unfold or 0 m) rfl
theorem lor_zero_right : ∀ n : Nat, Nat.lor n 0 = n
  | 0 => Eq.trans (bitwise_unfold or 0 0) rfl
  | n + 1 => Eq.trans (bitwise_unfold or (n + 1) 0) rfl

theorem lor_rec (x y : Nat) :
    Nat.lor x y = Nat.add (Nat.add (Nat.lor (Nat.div x 2) (Nat.div y 2)) (Nat.lor (Nat.div x 2) (Nat.div y 2)))
      (Nat.div (Nat.add (Nat.add (Nat.mod x 2) (Nat.mod y 2)) 1) 2) := by
  have hb : LT.lt (Nat.mod y 2) 2 := mod_lt y 2 two_pos
  have ha : LT.lt (Nat.mod x 2) 2 := mod_lt x 2 two_pos
  refine Eq.trans (bitwise_unfold or x y) ?_
  cases x with
  | zero =>
    show y = Nat.add (Nat.add (Nat.lor 0 (Nat.div y 2)) (Nat.lor 0 (Nat.div y 2))) (Nat.div (Nat.add (Nat.add 0 (Nat.mod y 2)) 1) 2)
    rw [lor_zero_left]; exact (Eq.trans (congrArg (Nat.add (Nat.add (Nat.div y 2) (Nat.div y 2))) (bit_or0 (Nat.mod y 2) hb)) (half y)).symm
  | succ x =>
    cases y with
    | zero =>
      show x + 1 = Nat.add (Nat.add (Nat.lor (Nat.div (x+1) 2) 0) (Nat.lor (Nat.div (x+1) 2) 0)) (Nat.div (Nat.add (Nat.add (Nat.mod (x+1) 2) 0) 1) 2)
      rw [lor_zero_right]; exact (Eq.trans (congrArg (Nat.add (Nat.add (Nat.div (x+1) 2) (Nat.div (x+1) 2))) (bit_or0' (Nat.mod (x+1) 2) ha)) (half (x+1))).symm
    | succ y => exact lor_bit _ _ _ ha hb

theorem xor_bit (r a b : Nat) (ha : LT.lt a 2) (hb : LT.lt b 2) :
    (if (bne (decide (a = 1)) (decide (b = 1))) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.mod (Nat.add a b) 2) :=
  bits (fun a b => (if (bne (decide (a = 1)) (decide (b = 1))) = true then r + r + 1 else r + r) = Nat.add (Nat.add r r) (Nat.mod (Nat.add a b) 2))
    rfl rfl rfl rfl a b ha hb

theorem bit_x0 (b : Nat) (hb : LT.lt b 2) : Nat.mod (Nat.add 0 b) 2 = b :=
  bit (fun b => Nat.mod (Nat.add 0 b) 2 = b) rfl rfl b hb

theorem bit_x0' (a : Nat) (ha : LT.lt a 2) : Nat.mod (Nat.add a 0) 2 = a :=
  bit (fun a => Nat.mod (Nat.add a 0) 2 = a) rfl rfl a ha

theorem xor_zero_left (m : Nat) : Nat.xor 0 m = m := Eq.trans (bitwise_unfold bne 0 m) rfl
theorem xor_zero_right : ∀ n : Nat, Nat.xor n 0 = n
  | 0 => Eq.trans (bitwise_unfold bne 0 0) rfl
  | n + 1 => Eq.trans (bitwise_unfold bne (n + 1) 0) rfl

theorem xor_rec (x y : Nat) :
    Nat.xor x y = Nat.add (Nat.add (Nat.xor (Nat.div x 2) (Nat.div y 2)) (Nat.xor (Nat.div x 2) (Nat.div y 2)))
      (Nat.mod (Nat.add (Nat.mod x 2) (Nat.mod y 2)) 2) := by
  have hb : LT.lt (Nat.mod y 2) 2 := mod_lt y 2 two_pos
  have ha : LT.lt (Nat.mod x 2) 2 := mod_lt x 2 two_pos
  refine Eq.trans (bitwise_unfold bne x y) ?_
  cases x with
  | zero =>
    show y = Nat.add (Nat.add (Nat.xor 0 (Nat.div y 2)) (Nat.xor 0 (Nat.div y 2))) (Nat.mod (Nat.add 0 (Nat.mod y 2)) 2)
    rw [xor_zero_left]; exact (Eq.trans (congrArg (Nat.add (Nat.add (Nat.div y 2) (Nat.div y 2))) (bit_x0 (Nat.mod y 2) hb)) (half y)).symm
  | succ x =>
    cases y with
    | zero =>
      show x + 1 = Nat.add (Nat.add (Nat.xor (Nat.div (x+1) 2) 0) (Nat.xor (Nat.div (x+1) 2) 0)) (Nat.mod (Nat.add (Nat.mod (x+1) 2) 0) 2)
      rw [xor_zero_right]; exact (Eq.trans (congrArg (Nat.add (Nat.add (Nat.div (x+1) 2) (Nat.div (x+1) 2))) (bit_x0' (Nat.mod (x+1) 2) ha)) (half (x+1))).symm
    | succ y => exact xor_bit _ _ _ ha hb


end Lean0
