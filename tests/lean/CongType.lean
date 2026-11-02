/-! Congruence results typed at `τ(x)`: `defeq` by the binder (or application, or constant)
congruence rule types `x` from its parts, while `infer x` may give a syntactically different
type from a typing handle (`OptionT.run_liftWith`: `MonadControlT.stM m m _ σ` against `σ`
itself). The rule's result is cast to `infer x`'s type. Found by the all-of-Init census. -/
-- lean0-export: OptionT.run_liftWith
