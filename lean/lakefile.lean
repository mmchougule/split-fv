import Lake
open Lake DSL

package «split-fv» where
  -- pure-Nat model, no mathlib dependency, so CI builds fast.

lean_lib «Split» where
  -- proofs live under Split/

@[default_target]
lean_lib «SplitFV» where
  roots := #[`Split]
