/-! Typing handles that meet themselves: in `Nat.gcd`'s well-founded unfolding equation, typing
a handle's argument reaches a term with the same handle, which recursed until the stack
overflowed (`Elab::infer` now takes a handle out of the map before using it). -/
-- lean0-export: _private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def
