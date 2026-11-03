/-! Milestone 5 test module: Nat and string literals, and the operations the kernel computes
on literals. -/
-- lean0-export: lit_zero lit_succ lit_add lit_succ_red lit_mul_big lit_sub lit_sub0 lit_beq_t lit_beq_f lit_ble_t lit_ble_f lit_lt lit_big_decide lit_pow lit_shl lit_shr lit_div lit_mod lit_gcd lit_gcd2 lit_land lit_lor lit_xor lit_rec dbl_ex

theorem lit_zero : (0 : Nat) = Nat.zero := rfl
theorem lit_succ : (5 : Nat) = Nat.succ 4 := rfl
theorem lit_add : 2 + 2 = 4 := rfl
theorem lit_succ_red : Nat.succ 5 = 6 := rfl
theorem lit_mul_big : 12345678901234567890 * 98765432109876543210 = 1219326311370217952237463801111263526900 := rfl
theorem lit_sub : 10 - 3 = 7 := rfl
theorem lit_sub0 : 3 - 10 = 0 := rfl
theorem lit_beq_t : Nat.beq 3 3 = true := rfl
theorem lit_beq_f : Nat.beq 3 4 = false := rfl
theorem lit_ble_t : Nat.ble 3 5 = true := rfl
theorem lit_ble_f : Nat.ble 5 3 = false := rfl
theorem lit_lt : (10 : Nat) < 20 := by decide
theorem lit_big_decide : 18446744073709551616 * 3 ≠ 55340232221128654849 := by decide
theorem lit_pow : 2 ^ 64 = 18446744073709551616 := rfl
theorem lit_shl : 1 <<< 10 = 1024 := rfl
-- `Nat.shiftRight` is computed a shift at a time, from its equations and `Nat.div`
theorem lit_shr : 1000 >>> 3 = 125 := rfl
-- the division-like operations: rules over Lean4Lean's checks of the fuel and
-- well-founded recursions
theorem lit_div : 1000 / 7 = 142 := rfl
theorem lit_mod : 1000 % 7 = 6 := rfl
theorem lit_gcd : Nat.gcd 48 18 = 6 := rfl
theorem lit_gcd2 : Nat.gcd 18 48 = 6 := rfl
theorem lit_land : 12 &&& 10 = 8 := rfl
theorem lit_lor : 12 ||| 10 = 14 := rfl
theorem lit_xor : 12 ^^^ 10 = 6 := rfl
def dbl (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih + 2) n
theorem lit_rec : dbl 3 = 6 := rfl
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
theorem dbl_ex : fact 5 = 120 := rfl
