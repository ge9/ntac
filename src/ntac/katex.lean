import data.rbmap
open lean
meta mutual def mparse_math_macro_aux, mparse_math_macro_aux2
with mparse_math_macro_aux: list string → string → list char → string
| ls acc [] := acc
| ls acc ('⟨' :: s):= mparse_math_macro_aux2 ls acc "" s
| ls acc (c :: s) := mparse_math_macro_aux ls (acc++c.to_string) s
with mparse_math_macro_aux2: list string → string → string → list char → string
| ls acc1 acc2 [] := "error: '⟩' expected"
| ls acc1 acc2 ('⟩'::s) := mparse_math_macro_aux ls (acc1++(ls.nth acc2.to_nat).get_or_else "!NTAC_IndexOutOfRange!") s -- todo: use acc2
| ls acc1 acc2 (c::s) := mparse_math_macro_aux2 ls acc1 (acc2++c.to_string) s

meta def mparse_math_macro (ls: list string) (s: list char) : string :=
mparse_math_macro_aux ls "" s 
open expr

namespace string
meta def replace_char_aux : list char → char → list char → list char
| [] _ _ := []
| (c::cs) cr s := let csr := replace_char_aux cs cr s in
if c=cr then s++csr else c::csr

meta def replace_char (org:string) (search: char) (repl: string) :string:= (replace_char_aux org.to_list search repl.to_list).as_string
meta def replace_char_list : string → (list (char × string) ) → string:= 
λ s lp,
match lp with
| x :: xs :=  replace_char_list (let ⟨c, s1⟩ := x in s.replace_char c s1) xs
| [] := s
end
end string

--hard-coded conversion rules from `expr` to KaTeX
--TODO: collect information from `doc_string`
--Four backslashes because both Lean and KaTeX need escaping them.
def parse_rules :=
rbmap.from_list [
("eq", 2,"⟨0⟩ = ⟨1⟩")
,("ne", 2,"⟨0⟩ \\neq ⟨1⟩")
,("has_le.le", 2,"⟨0⟩ \\le ⟨1⟩")
,("has_lt.lt", 2,"⟨0⟩ \\lt ⟨1⟩")
,("ge", 2,"⟨0⟩ \\ge ⟨1⟩")
,("gt", 2,"⟨0⟩ \\gt ⟨1⟩")
,("nat.min_fac", 1," \\text{the least prime factor of } ⟨0⟩")
,("nat.prime", 1,"⟨0⟩ \\text{is prime }")
,("nat.factorial", 1,"⟨0⟩!")
,("not", 1,"\\neg ⟨0⟩")
,("and", 2,"⟨0⟩ \\wedge ⟨1⟩")
,("or", 2,"⟨0⟩ \\vee ⟨1⟩")
,("coe", 1,"⟨0⟩")
,("has_add.add", 2,"⟨0⟩ + ⟨1⟩")
,("has_mod.mod", 2,"⟨0⟩ \\% ⟨1⟩")
,("has_sub.sub", 2,"⟨0⟩ - ⟨1⟩")
,("has_div.div", 2,"\\frac{⟨0⟩}{⟨1⟩}")
,("has_mul.mul", 2,"⟨0⟩⟨1⟩")
,("has_pow.pow", 2,"{⟨0⟩}^{⟨1⟩}")
,("has_dvd.dvd", 2,"⟨0⟩ \\mid ⟨1⟩")
,("has_dvd.dvd", 2,"⟨0⟩ \\mid ⟨1⟩")
,("iff.mpr", 1,"\\text{right dir of} ⟨0⟩")
--,("Exists", 1,"\\Exist⟨0⟩")
]
--変数が2文字以上だったらLaTeXの\text{}にして_を\_に変換
meta def string.var_to_text (s: string): string := if s.length <= 1 then s else ("\\text{"++s++"}").replace_char '_' "\\_" 

meta def get_last_n_args_aux : ℕ → expr → list expr → list expr
| 0 _  acc := acc
| (nat.succ n) (app f x) acc := get_last_n_args_aux n f (x::acc)
| (nat.succ n) _ acc := acc
meta def get_last_n_args : ℕ → expr → list expr
| n e := get_last_n_args_aux n e []

meta def replace_for_katex (s : string) := s.replace_char_list 
[('_', "\\_"), ('<', "$\\lt$"), ( '≠', "$\\ne$"), ( '^', "\\^")]

/--run tactic without changing tactic_state-/
meta def safe_run {α }(tac: tactic α ):tactic α := do r ← tactic.read, e← tac, tactic.write r, return e
/--converts `expr` to `string`, usinc tactic monad-/
meta def expr_to_katex : expr → tactic string
| e :=  do ppe ← tactic.pp e,
        let fallback_res := "\\text{"++replace_for_katex ppe.to_string++"}" in
        if e.is_numeral then return ppe.to_string else
        match e with
        | (const n ls) := return n.to_string.var_to_text
        | (local_const n m bi t) := return m.to_string.var_to_text
        --Use "∀" for Prop and "Π" for others. Refer to `tactic.mk_local_pis` for the treatment of de-Bruijn index. 
        --TODO: expand multiple pi arguments at once (not ∀x, ∀y, P(x, y) but ∀xy, P(x, y)). see `expr.pi_arity`.
        | (pi n bi d b) :=     (do  p ← tactic.mk_local' n bi d, let b2 := expr.instantiate_var b p, tstr ← safe_run $ tactic.infer_type b2 >>= tactic.pp, 
                           body ← expr_to_katex b2,return $ (if tstr.to_string = "Prop" then "\\forall " else "\\Pi") ++(n.to_string)++", "++body)
        | `(Exists (%%b : %%_ → Prop)) := match b with
            | (lam n bi d b) := (do p ← tactic.mk_local' n bi d, let b2 := expr.instantiate_var b p, tstr ← safe_run $ tactic.infer_type b2 >>= tactic.pp, 
                           body ← expr_to_katex b2,return $                                               "\\exists " ++(n.to_string)++", "++body)
            | _ := do tactic.trace "unsupported `Exists` formula", return fallback_res
            end
        | (app _ _) := let n := e.get_app_fn.const_name.to_string in do --tactic.trace $ e.get_app_fn,
                        ( match parse_rules.find n with
                          | some rule := do ls ← monad.sequence $ list.map expr_to_katex $ get_last_n_args rule.1 e,
                                            return $ mparse_math_macro ls rule.2.to_list
                          | none := match e.get_app_fn with
                                    | (local_const n m bi t) := do args ← monad.sequence $ e.get_app_args.map expr_to_katex, 
                                      (return $ m.to_string.var_to_text++"("++",".intercalate args++")")--to ordinary function notation
                                    | _:= do tactic.trace $ "unsupported function name: "++n, return fallback_res
                                    end
                          end)
        | _ := (do tactic.trace "unsupported expr form", return fallback_res)

      end