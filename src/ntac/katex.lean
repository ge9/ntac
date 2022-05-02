open lean

meta mutual def mparse_math_macro_aux, mparse_math_macro_aux2
with mparse_math_macro_aux: list string → string → list char → string
| ls acc [] := acc
| ls acc ('⟨' :: s):= mparse_math_macro_aux2 ls acc "" s
| ls acc (c :: s) := mparse_math_macro_aux ls (acc++c.to_string) s
with mparse_math_macro_aux2: list string → string → string → list char → string
| ls acc1 acc2 [] := "error: '⟩' expected"
| ls acc1 acc2 ('⟩'::s) := mparse_math_macro_aux ls (acc1++(ls.nth acc2.to_nat).get_or_else "!IndexOutOfRange!") s -- todo: use acc2
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
end string

--hard-coded conversion rules from `expr` to KaTeX
--TODO: collect information from `doc_string`
--Four backslashes because both Lean and KaTeX need escaping them.
def parse_rules :=
rbmap.from_list [
("eq", 2,"⟨0⟩ = ⟨1⟩"),
("ne", 2,"⟨0⟩ \\\\neq ⟨1⟩"),
("has_le.le", 2,"⟨0⟩ \\\\le ⟨1⟩"),
("ge", 2,"⟨0⟩ \\\\ge ⟨1⟩"),
("nat.min_fac", 1," \\\\text{the least prime factor of } ⟨0⟩"),
("nat.prime", 1,"⟨0⟩ \\\\text{is prime }"),
("nat.factorial", 1,"⟨0⟩!"),
("not", 1,"\\\\neg ⟨0⟩"),
("and", 2,"⟨0⟩ \\\\wedge ⟨1⟩"),
("or", 2,"⟨0⟩ \\\\vee ⟨1⟩"),
("coe", 1,"⟨0⟩"),
("has_add.add", 2,"⟨0⟩ + ⟨1⟩"),
("has_mod.mod", 2,"⟨0⟩ \\\\% ⟨1⟩"),
("has_sub.sub", 2,"⟨0⟩ - ⟨1⟩"),
("has_div.div", 2,"\\\\frac{⟨0⟩}{⟨1⟩}"),
("has_mul.mul", 2,"⟨0⟩⟨1⟩"),
("has_pow.pow", 2,"{⟨0⟩}^{⟨1⟩}"),
("has_dvd.dvd", 2,"⟨0⟩ \\\\mid ⟨1⟩"),
("pythagorean_triple.is_primitive_classified_aux" , 8, "pythagorean\\\\_triple.is\\\\_primitive\\\\_classified\\\\_aux \\\\: ⟨0⟩\\\\:⟨1⟩\\\\:⟨2⟩\\\\:⟨3⟩\\\\:⟨4⟩\\\\:⟨5⟩\\\\:⟨6⟩\\\\:⟨7⟩")
]
meta def get_last_n_args_aux : ℕ → expr → list expr → list expr
| 0 _  acc := acc
| (nat.succ n) (app f x) acc := get_last_n_args_aux n f (x::acc)
| (nat.succ n) _ acc := acc
meta def get_last_n_args : ℕ → expr → list expr
| n e := get_last_n_args_aux n e []

/--converts `expr` to `string`, usinc tactic monad-/
meta def expr_to_katex : expr → tactic string
| e :=  do ppe ← tactic.pp e,
        if e.is_numeral then return ppe.to_string else
        if e.is_constant then return $ (const_name e).to_string.replace_char '_' "\\\\_" else
        if e.is_local_constant then return $ (local_pp_name e).to_string.replace_char '_' "\\\\_" else
        if ¬e.is_app then return ppe.to_string else
        let n := e.get_app_fn.const_name in do 
        --tactic.trace n,
        ( match parse_rules.find n.to_string with
           | some tex := do ls ← monad.sequence $ list.map expr_to_katex $ get_last_n_args tex.1 e,
                            return $ mparse_math_macro ls tex.2.to_list
           | none := return ppe.to_string
           end)
