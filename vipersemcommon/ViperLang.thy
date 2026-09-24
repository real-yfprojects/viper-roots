theory ViperLang
  imports Main HOL.Real "HOL-Eisbach.Eisbach_Tools"
begin

(* TODO:
- Add perm expressions
- Add predicates
- Add wf_state (Viper state)
- Add function calls
- Add domains
- Add pure exists and forall
*)

(* No way to express references, domains *)
datatype lit = LBool bool | LInt int | LNull | LPerm real

abbreviation NoPerm where "NoPerm \<equiv> LPerm 0"
abbreviation WritePerm where "WritePerm \<equiv> LPerm 1"


datatype binop =
  Add | Sub | Mult | IntDiv | PermDiv | Mod
| Eq | Neq
| Gt | Gte | Lt | Lte
| Or | BImp | And

datatype unop = Not | Minus

type_synonym predicate_ident = string
type_synonym method_ident = string
type_synonym field_ident = string
type_synonym function_ident = string
type_synonym label = string
type_synonym var = nat

type_synonym abs_type = string

datatype vtyp = TInt | TBool | TPerm | TRef | TAbs abs_type

primrec type_of_lit :: "lit \<Rightarrow> vtyp"
  where
   "type_of_lit (LBool b) = TBool"
 | "type_of_lit (LInt i) = TInt"
 | "type_of_lit (LPerm _) = TPerm"
 | "type_of_lit LNull = TRef"

datatype pure_exp =
  ELit lit
  | Var var
  | Unop unop pure_exp
  | Binop pure_exp binop pure_exp
  | CondExp pure_exp pure_exp pure_exp
  | FieldAcc pure_exp field_ident
  | Old label pure_exp

  | Perm pure_exp field_ident
  | PermPred predicate_ident "pure_exp list"

  | FunApp function_ident "pure_exp list"
  | Result (* Only for functions *)

\<comment>\<open>unfolding P(l) in e\<close>
  | Unfolding predicate_ident "pure_exp list" pure_exp

  | Let pure_exp pure_exp
  | PExists vtyp pure_exp
  | is_pforall: PForall vtyp pure_exp

  | DummyExpr  \<comment> \<open>for ill-formed substitution\<close>

datatype 'p exp_or_wildcard = PureExp 'p | Wildcard

datatype 'p atomic_assert =
  is_pure_atomic: Pure 'p
  | Acc 'p field_ident "'p exp_or_wildcard"
  | AccPredicate predicate_ident "'p list" "'p exp_or_wildcard"
(* AccPredicate "name of predicate" "arguments" "permission amount" *)

datatype ('p, 'atm) assert =
  Atomic 'atm
  | Imp 'p "('p, 'atm) assert"
  | CondAssert 'p "('p, 'atm) assert" "('p, 'atm) assert"
(*
  | InhaleExhale "('p, 'atm) assert" "('p, 'atm) assert"
*)
  | ImpureAnd "('p, 'atm) assert" "('p, 'atm) assert"
  | ImpureOr "('p, 'atm) assert" "('p, 'atm) assert"

  | Star "('p, 'atm) assert" "('p, 'atm) assert" (infixl "&&" 60)
  | Wand "('p, 'atm) assert" "('p, 'atm) assert" (infixl "--*" 60)

  | is_forall: ForAll vtyp "('p, 'atm) assert"
  | Exists vtyp "('p, 'atm) assert"

text \<open>Assertions \<^typ>\<open>('p, 'atm) assert\<close> are parametrized by the pure expressions \<^typ>\<open>'p\<close> as well as the
atomic assertions \<^typ>\<open>'atm\<close> (assertions without impure connectives). Note that the atomic assertions usually include
the pure assertions.\<close>

text\<open>We prove the following instantiation for Viper assertions.\<close>
type_synonym assertion = "(pure_exp, pure_exp atomic_assert) assert"

term "(Atomic (AccPredicate name [] Wildcard)) :: assertion"


fun is_pure :: "assertion \<Rightarrow> bool" where
  "is_pure (Atomic e) \<longleftrightarrow> is_pure_atomic e"
| "is_pure (Imp _ A) \<longleftrightarrow> is_pure A"
| "is_pure (CondAssert _ A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (A && B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ImpureAnd A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ImpureOr A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ForAll _ A) \<longleftrightarrow> is_pure A"
| "is_pure (Exists _ A) \<longleftrightarrow> is_pure A"
| "is_pure (Wand _ _) \<longleftrightarrow> False"

(* currently missing:
- x := new(_)
- goto
- inhale-exhale
*)

datatype stmt =

\<comment>\<open>Assertions\<close>
  Inhale assertion | Exhale assertion | Assert assertion | Assume assertion
\<comment>\<open>assume A not valid in the theoretical semantics\<close>

\<comment>\<open>Control structures\<close>
| If pure_exp stmt stmt | Seq stmt stmt

\<comment>\<open>Assignments\<close>
| LocalAssign var pure_exp | FieldAssign pure_exp field_ident pure_exp | Havoc var

\<comment>\<open>Calls and loops\<close>
| MethodCall "var list" method_ident "pure_exp list" (* y1,y2,... := m(e1, e2, ...) *)
| While pure_exp assertion stmt (* While (b) invariant I {s} *)

\<comment>\<open>Verifier directives\<close>
| Unfold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Fold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Package assertion assertion
| Apply assertion assertion

\<comment>\<open>Misc\<close>
| Label label | Scope vtyp stmt | Skip

(* method m(x) returns y req P ens Q *)
record method_decl =
  args :: "vtyp list"
  rets :: "vtyp list"
  pre :: assertion
  post :: assertion
  body :: "stmt option" (* Abstract or concrete *)

record predicate_decl =
  args :: "vtyp list"
  body :: "assertion option"

record function_decl =
  args :: "vtyp list"
  ret :: vtyp
  pre :: assertion
  post :: "assertion option" (* difference between post (terminating) and no post? *)
  body :: "pure_exp option" (* Abstract or concrete *)

record program =
  "methods" :: "method_ident \<rightharpoonup> method_decl"
  predicates :: "predicate_ident \<rightharpoonup> predicate_decl"
  funs :: "function_ident \<rightharpoonup> function_decl"
  declared_fields :: "field_ident \<rightharpoonup> vtyp"
  domains :: nat (* TODO *)

(* well-formed program:
- Method calls are well-formed (method exists, right number of args and return, right types
- Same for functions calls
- Fields exist (+ typing)
- Predicate (like methods)
- Domain (typing?)
- Typing
- Variables that do not exist

\<Longrightarrow> If a program is well-formed and well-typed, all expressions must reduce
*)

(* Well-definedness:
- Variables are defined
- Same number of variables for args and rets in method calls
- labels are unique in a method body
- all methods called exist
- No "lhs" (wands) or "default" (methods, loops?) label
- No contravariant recursion for predicates
- Right fields
*)

definition label_lhs :: "label" where
  "label_lhs = ''lhs''"

definition empty_label :: "label" where
  "empty_label = ''''"

record configuration =
  angelic_exhale :: bool
  executable :: bool
  annotation :: "bool option" (* None = angelic, false = ignored, true = used *)
  ghost_assert :: bool (* fold unfold apply package: either assert, or skip *)

datatype RedType = RInhale | RExhale





section \<open>Shorthands\<close>

(*
fun n_scope :: "vtyp list \<Rightarrow> stmt \<Rightarrow> stmt" where
  "n_scope [] s = s"
| "n_scope (t # q) s = Scope t (n_scope q s)"
*)

fun n_havoc :: "var list \<Rightarrow> stmt" where
  "n_havoc [] = Skip"
| "n_havoc (x # q) = Seq (Havoc x) (n_havoc q)"

fun n_forall :: "vtyp list \<Rightarrow> assertion \<Rightarrow> assertion" where
  "n_forall [] A = A"
| "n_forall (t # q) A = ForAll t (n_forall q A)"

fun n_forall_pure :: "vtyp list \<Rightarrow> pure_exp \<Rightarrow> pure_exp" where
  "n_forall_pure [] e = e"
| "n_forall_pure (t # q) e = PForall t (n_forall_pure q e)"

section \<open>Recursive predicates on syntax\<close>

fun pure_exp_pred_rec :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> pure_exp \<Rightarrow> bool" and
    pure_exp_pred :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> pure_exp \<Rightarrow> bool"
    where
  "pure_exp_pred p e \<longleftrightarrow> (p e \<and> pure_exp_pred_rec p e)"
| "pure_exp_pred_rec p (Var x) \<longleftrightarrow> True"
| "pure_exp_pred_rec p (ELit lit) \<longleftrightarrow> True"
| "pure_exp_pred_rec p (Unop uop e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Binop e1 bop e2) \<longleftrightarrow> pure_exp_pred p e1 \<and> pure_exp_pred p e2"
| "pure_exp_pred_rec p (CondExp cond e1 e2) \<longleftrightarrow> pure_exp_pred p cond \<and> pure_exp_pred p e1 \<and> pure_exp_pred p e2"
| "pure_exp_pred_rec p (FieldAcc e f) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Old lbl e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Perm e f) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (PermPred pname es) \<longleftrightarrow> list_all (pure_exp_pred p) es"
| "pure_exp_pred_rec p (FunApp f es) \<longleftrightarrow> list_all (pure_exp_pred p) es"
| "pure_exp_pred_rec p Result \<longleftrightarrow> True"
| "pure_exp_pred_rec p (Unfolding pname es e) \<longleftrightarrow> list_all (pure_exp_pred p) es \<and> pure_exp_pred p e"
| "pure_exp_pred_rec p (pure_exp.Let e e_body) \<longleftrightarrow> pure_exp_pred p e \<and> pure_exp_pred p e_body"
| "pure_exp_pred_rec p (PExists ty e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (PForall ty e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p DummyExpr \<longleftrightarrow> True"

\<comment> \<open>We tweak the simp rules for pure_exp_pred such that it is only unfolded for concrete arguments.\<close>
declare pure_exp_pred.simps[simp del]
lemmas pure_exp_pred_simps[simp] =
  pure_exp_pred.simps[where ?e="Var _"]
  pure_exp_pred.simps[where ?e="ELit _"]
  pure_exp_pred.simps[where ?e="Unop _ _"]
  pure_exp_pred.simps[where ?e="Binop _ _ _"]
  pure_exp_pred.simps[where ?e="CondExp _ _ _"]
  pure_exp_pred.simps[where ?e="FieldAcc _ _"]
  pure_exp_pred.simps[where ?e="Old _ _"]
  pure_exp_pred.simps[where ?e="Perm _ _"]
  pure_exp_pred.simps[where ?e="PermPred _ _"]
  pure_exp_pred.simps[where ?e="FunApp _ _"]
  pure_exp_pred.simps[where ?e="Result"]
  pure_exp_pred.simps[where ?e="Unfolding _ _ _"]
  pure_exp_pred.simps[where ?e="Let _ _"]
  pure_exp_pred.simps[where ?e="PExists _ _"]
  pure_exp_pred.simps[where ?e="PForall _ _"]

fun
  atomic_assert_pred :: "(pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert) \<Rightarrow> bool" and
  atomic_assert_pred_rec :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert) \<Rightarrow> bool"
  where
  "atomic_assert_pred p_atm p_e A_atm \<longleftrightarrow> p_atm A_atm \<and> atomic_assert_pred_rec p_e A_atm"
| "atomic_assert_pred_rec p_e (Pure e) \<longleftrightarrow> pure_exp_pred p_e e"
| "atomic_assert_pred_rec p_e (Acc e f Wildcard) \<longleftrightarrow> pure_exp_pred p_e e"
| "atomic_assert_pred_rec p_e (Acc e1 f (PureExp e2)) \<longleftrightarrow> pure_exp_pred p_e e1 \<and> pure_exp_pred p_e e2"
| "atomic_assert_pred_rec p_e (AccPredicate pname es Wildcard) \<longleftrightarrow> list_all (pure_exp_pred p_e) es"
| "atomic_assert_pred_rec p_e (AccPredicate pname es (PureExp e2)) \<longleftrightarrow> (list_all (pure_exp_pred p_e) es) \<and> pure_exp_pred p_e e2"

declare atomic_assert_pred.simps[simp del]
lemmas atomic_assert_pred_simps[simp] =
  atomic_assert_pred.simps[where ?A_atm="Pure _"]
  atomic_assert_pred.simps[where ?A_atm="Acc _ _ _"]
  atomic_assert_pred.simps[where ?A_atm="AccPredicate _ _ _"]

fun assert_pred :: "(assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> bool" and
    assert_pred_rec :: "(assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow>  bool"
  where
  "assert_pred p_assert p_atm p_e A \<longleftrightarrow> p_assert A \<and> assert_pred_rec p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Atomic A_atm) \<longleftrightarrow> atomic_assert_pred p_atm p_e A_atm"
| "assert_pred_rec p_assert p_atm p_e (Imp e A) \<longleftrightarrow> pure_exp_pred p_e e \<and> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (CondAssert e A B) \<longleftrightarrow> pure_exp_pred p_e e \<and> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (A && B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ImpureAnd A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ImpureOr A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ForAll _ A) \<longleftrightarrow> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Exists _ A) \<longleftrightarrow> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Wand A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"

declare assert_pred.simps[simp del]
lemmas assert_pred_simps[simp] =
  assert_pred.simps[where ?A="Atomic _"]
  assert_pred.simps[where ?A="Imp _ _"]
  assert_pred.simps[where ?A="CondAssert _ _ _"]
  assert_pred.simps[where ?A="Star _ _"]
  assert_pred.simps[where ?A="ImpureAnd _ _"]
  assert_pred.simps[where ?A="ImpureOr _ _"]
  assert_pred.simps[where ?A="ForAll _ _"]
  assert_pred.simps[where ?A="Exists _ _"]
  assert_pred.simps[where ?A="Wand _ _"]

fun stmt_pred :: "(stmt \<Rightarrow> bool) \<Rightarrow> (assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> stmt \<Rightarrow> bool" and
    stmt_pred_rec :: "(stmt \<Rightarrow> bool) \<Rightarrow> (assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> stmt \<Rightarrow> bool"
    where
  "stmt_pred p_stmt p_assert p_e s \<longleftrightarrow> p_stmt s \<and> stmt_pred_rec p_stmt p_assert p_e s"
| "stmt_pred_rec p_stmt p_assert p_e (Inhale A) \<longleftrightarrow> p_assert A"
| "stmt_pred_rec p_stmt p_assert p_e (Exhale A) \<longleftrightarrow> p_assert A"
| "stmt_pred_rec p_stmt p_assert p_e (Assert A) \<longleftrightarrow> p_assert A"
| "stmt_pred_rec p_stmt p_assert p_e (Assume A) \<longleftrightarrow> p_assert A"
| "stmt_pred_rec p_stmt p_assert p_e (LocalAssign x e) \<longleftrightarrow> p_e e"
| "stmt_pred_rec p_stmt p_assert p_e (FieldAssign e1 f e2) \<longleftrightarrow> p_e e1 \<and> p_e e2"
| "stmt_pred_rec p_stmt p_assert p_e (Havoc x) \<longleftrightarrow> True"
| "stmt_pred_rec p_stmt p_assert p_e (If e s1 s2) \<longleftrightarrow> p_e e \<and> stmt_pred p_stmt p_assert p_e s1 \<and> stmt_pred p_stmt p_assert p_e s2"
| "stmt_pred_rec p_stmt p_assert p_e (Seq s1 s2) \<longleftrightarrow> stmt_pred p_stmt p_assert p_e s1 \<and> stmt_pred p_stmt p_assert p_e s2"
| "stmt_pred_rec p_stmt p_assert p_e (MethodCall ys m es) \<longleftrightarrow> list_all p_e es"
| "stmt_pred_rec p_stmt p_assert p_e (While e A s) \<longleftrightarrow> p_e e \<and> p_assert A \<and> p_stmt s"
| "stmt_pred_rec p_stmt p_assert p_e (Unfold pred es p) \<longleftrightarrow> list_all p_e es" \<comment>\<open>TODO: restrict p\<close>
| "stmt_pred_rec p_stmt p_assert p_e (Fold pred es p) \<longleftrightarrow> list_all p_e es" \<comment>\<open>TODO: restrict p\<close>
| "stmt_pred_rec p_stmt p_assert p_e (Package A B) \<longleftrightarrow> p_assert A \<and> p_assert B"
| "stmt_pred_rec p_stmt p_assert p_e (Apply A B) \<longleftrightarrow> p_assert A \<and> p_assert B"
| "stmt_pred_rec p_stmt p_assert p_e (Label lbl) \<longleftrightarrow> True"
| "stmt_pred_rec p_stmt p_assert p_e (Scope vty s) \<longleftrightarrow> stmt_pred p_stmt p_assert p_e s"
| "stmt_pred_rec p_stmt p_assert p_e Skip \<longleftrightarrow> True"

declare stmt_pred.simps[simp del]
lemmas stmt_pred_simps[simp] =
  stmt_pred.simps[where ?s="stmt.Inhale _"]
  stmt_pred.simps[where ?s="stmt.Exhale _"]
  stmt_pred.simps[where ?s="stmt.Assert _"]
  stmt_pred.simps[where ?s="stmt.Assume _"]
  stmt_pred.simps[where ?s="stmt.LocalAssign _ _"]
  stmt_pred.simps[where ?s="stmt.FieldAssign _ _ _"]
  stmt_pred.simps[where ?s="stmt.Havoc _"]
  stmt_pred.simps[where ?s="stmt.If _ _ _"]
  stmt_pred.simps[where ?s="stmt.Seq _ _"]
  stmt_pred.simps[where ?s="stmt.MethodCall _ _ _"]
  stmt_pred.simps[where ?s="stmt.While _ _ _"]
  stmt_pred.simps[where ?s="stmt.Unfold _ _ _"]
  stmt_pred.simps[where ?s="stmt.Fold _ _ _"]
  stmt_pred.simps[where ?s="stmt.Package _ _"]
  stmt_pred.simps[where ?s="stmt.Apply _ _"]
  stmt_pred.simps[where ?s="stmt.Label _"]
  stmt_pred.simps[where ?s="stmt.Scope _ _"]
  stmt_pred.simps[where ?s="stmt.Skip"]

end
