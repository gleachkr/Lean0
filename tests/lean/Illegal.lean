/-! Legal inductive blocks whose illegal variants the schema must reject. Lean's kernel refuses
to elaborate an illegal block, so no module can export one: `scripts/illegal-export.py` makes
each variant by one change to this module's export (a constructor's domain, a universe, a
recursor's motive, ...), and `scripts/test.sh` runs `lean0 gen --unchecked` on it, which skips
nanoda's check so that the schema alone judges the block. This module itself is the control:
every block is certified by the schema. -/
-- lean0-export: NP Big PD A W V

-- an empty type, a harmless domain
inductive E : Type

-- `nonpositive`: `(E → NP) → NP` becomes `(NP → NP) → NP`
inductive NP : Type
  | mk : (E → NP) → NP

-- `universe`: `E → Big` becomes `Type → Big`
inductive Big : Type
  | mk : E → Big

-- `elim`: `PD.rec`'s motive `PD → Prop` becomes `PD → Sort u` (large elimination from a
-- proposition with two constructors)
inductive PD : Prop
  | a
  | b

-- `mutual`: `B : Type` becomes `B : Type 1` (a mutual block in two universes)
mutual
inductive A : Type
  | mk : B → A
inductive B : Type
  | mk : A → B
end

-- `result`: the constructor's result `W α` becomes `W (W α)`
inductive W (α : Type) : Type
  | mk : W α

-- `occurrence`: the field `V α` becomes `V (V α)` (an occurrence of the type not applied to
-- its parameter)
inductive V (α : Type) : Type
  | mk : V α → V α
