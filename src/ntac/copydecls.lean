--supplement missing tactics in `ntac.interactive` by those from `tactic.interactive`.

import ntac.ntac

open tactic
namespace ntac
meta def copy_decl (d : declaration) : tactic unit :=
do
 s ← read,
  match environment.get (tactic_state.env s) $ d.to_name.update_prefix `ntac.interactive with
| (exceptional.success _)      := do trace d.to_name, return ()
| (exceptional.exception _) := add_decl $ d.update_name $ d.to_name.update_prefix `ntac.interactive
end

--@[reducible] meta def filter (d : declaration) : bool :=
--d.to_name ∉ [`tactic.interactive.induction, `ntac.interactive.ap]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive) (copy_decl dec)
end ntac

--run_cmd ntac.copy_decls
