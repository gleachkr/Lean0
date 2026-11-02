/-! Milestone 5, heavy part: division, modulus, gcd, shiftRight and the bitwise operations on
literals, and string literals (whose expansion mentions `String.ofList`, defined through
UTF-8 encoding). These depend on well-founded recursion, whose lemmas take most of this
certificate (about 1 GB). Not run by scripts/test.sh: certify it with
`scripts/certify.sh tests/lean/heavy/LitHeavy.lean`, then delete build/gen/litheavy. -/
-- lean0-export: lit_div lit_mod lit_div0 lit_mod0 lit_gcd lit_gcd0 lit_gcd2 lit_shr lit_land lit_lor lit_xor str_eq

theorem lit_div : 100 / 7 = 14 := rfl
theorem lit_mod : 100 % 7 = 2 := rfl
theorem lit_div0 : 5 / 0 = 0 := rfl
theorem lit_mod0 : 5 % 0 = 5 := rfl
theorem lit_gcd : Nat.gcd 12 18 = 6 := rfl
theorem lit_gcd0 : Nat.gcd 0 5 = 5 := rfl
theorem lit_gcd2 : Nat.gcd 18 12 = 6 := rfl
theorem lit_shr : 1024 >>> 3 = 128 := rfl
theorem lit_land : Nat.land 12 10 = 8 := rfl
theorem lit_lor : Nat.lor 12 10 = 14 := rfl
theorem lit_xor : Nat.xor 12 10 = 6 := rfl
theorem str_eq : "ab" = String.ofList ['a', 'b'] := rfl
