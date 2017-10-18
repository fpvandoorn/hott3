/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

A tactic to instantiate axioms

To do:
copy attributes, add @[hott]
instantiate to families of constants satisfying the axioms

-/

namespace declaration

meta def is_axiom : declaration → bool
| (ax _ _ _)     := tt
| (cnst _ _ _ _) := tt
| _              := ff

end declaration

namespace tactic

open expr declaration

declare_trace instantiate_axioms

-- meta def replace_axioms (n m : name) (e : expr) : expr :=
-- e.replace (λe' _, 
--   match e' with
--   | const n' ls := some $ const (n'.replace_prefix n m) ls
--   | x := none
--   end)

meta def replace_axioms (n m : name) : expr → expr
| (const n' ls)   := const (n'.replace_prefix n m) ls
| (app e f)       := app (replace_axioms e) (replace_axioms f)
| (lam n' bi e t) := lam n' bi (replace_axioms e) (replace_axioms t)
| (pi n' bi e t)  := pi n' bi (replace_axioms e) (replace_axioms t)
| (elet n g e f)  := elet n (replace_axioms g) (replace_axioms e) (replace_axioms f)
| x               := x

meta def instantiate_definition (n m : name) (en : name) : declaration → declaration
| (defn n' ls t v h tr) := defn en ls (replace_axioms n m t) (replace_axioms n m v) h tr
| (thm n' ls t v)       := thm en ls (replace_axioms n m t) $ task.map (replace_axioms n m) v
| x                     := x

meta def replace_axioms_plus (n m : name) (t : name → declaration → tactic unit) : expr → tactic expr
| (const n' ls)  := 
if n.is_prefix_of n' 
then do let m' := n'.replace_prefix n m, 
env ← get_env,
match env.get m' with
  | exceptional.success e      := skip
  | exceptional.exception ._ _ := do d ← env.get n', t m' d
  end,
return $ const m' ls
else return $ const n' ls
| (app e f)       := do e' ← replace_axioms_plus e, f' ← replace_axioms_plus f, return $ app e' f'
| (lam n' bi e t) := do e' ← replace_axioms_plus e, t' ← replace_axioms_plus t, return $ lam n' bi e' t'
| (pi n' bi e t)  := do e' ← replace_axioms_plus e, t' ← replace_axioms_plus t, return $ pi n' bi e' t'
| (elet n' g e f) := do g' ← replace_axioms_plus g, e' ← replace_axioms_plus e, f' ← replace_axioms_plus f, return $ elet n' g' e' f'
| x               := return x

meta def instantiate_definition_plus (n m : name) : name → declaration → tactic unit
| en (defn n' ls t v h tr) := do when_tracing `instantiate_axioms $ trace $ to_fmt "begin add decl " ++ to_fmt en, t' ← replace_axioms_plus n m instantiate_definition_plus t, v' ← replace_axioms_plus n m instantiate_definition_plus v, when_tracing `instantiate_axioms $ trace $ to_fmt "end add decl " ++ to_fmt en, add_decl $ defn en ls t' v' h tr
| en (thm n' ls t v)       := do t' ← replace_axioms_plus n m instantiate_definition_plus t, v' ← replace_axioms_plus n m instantiate_definition_plus v.get, add_decl $ thm en ls t' (pure $ v')
| en x                     := fail $ to_fmt "Couldn't find definition: " ++ to_fmt en ++ " for corresponding axiom."

meta def instantiate_axioms (n m : name) : tactic unit :=
do env ← get_env,
env.fold skip $ λd t, 
  do t,
  let dn := d.to_name,
  if ¬n.is_prefix_of dn then skip 
  else do let en := dn.replace_prefix n m,
  env' ← get_env,
  match env'.get en with
  | exceptional.success e      := when_tracing `instantiate_axioms $ trace $ to_fmt "skipped " ++ to_fmt en
  | exceptional.exception ._ _ := instantiate_definition_plus n m en d
    --   | exceptional.exception ._ _ := if d.is_axiom then fail $ to_fmt "no such definition: " ++ to_fmt en
    -- else do let e := instantiate_definition n m en d,
    -- add_decl e <|> _
  end

  run_cmd instantiate_axioms `hott.modality `hott.prop_trunc

end tactic