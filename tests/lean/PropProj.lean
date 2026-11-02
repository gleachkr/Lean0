/-! Projections out of a structure that is a proposition only at some levels: `Exists.{0}` and
`Nonempty.{0}`, whose fields are then proofs (the `S_proj_i_dfp` axioms). -/
-- lean0-export: PropProj.snd PropProj.fst PropProj.ne

namespace PropProj

theorem fst (P : Prop) (Q : P → Prop) (h : ∃ x : P, Q x) : P := h.1
theorem snd (P : Prop) (Q : P → Prop) (h : ∃ x : P, Q x) : Q h.1 := h.2
theorem ne (P : Prop) (h : Nonempty P) : P := h.1

end PropProj
