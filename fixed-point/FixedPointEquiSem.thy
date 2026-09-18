theory FixedPointEquiSem
  imports Main ViperAbstract.Instantiation ViperCommon.ViperLang ViperCommon.SepAlgebra
begin

(* TODO:
3. Prove the predicate interpretation is monotone
4. conclude the lfp existence
5. Update the verifies proof in abstractrefinestotal to assume that the interp is the lsp of the predicates in the code
*)
(* TODO Explanation of theory file *)

section \<open>Monotony of Satisfiability\<close>

text \<open>To later show that the predicate evaluation operation is monotone,
we show helper lemmas in this section to establish monotony for subfunctions that
revolve around which states an assertion satisfies.\<close>

type_synonym assertion = "ViperLang.assertion"


(* lemma: sat_set is monotone
case distinction on the sat_set def
most cases should be trivial because they don't depend on the pinterp
 *)

lemma sat_set_mono:
  fixes body :: "assertion"
  shows "mono (\<lambda> pinterp. \<langle> \<lparr> domains = dinterp, predicates = pinterp, funs = finterp \<rparr>, F \<rangle> \<Turnstile> \<langle>body\<rangle> )" (is "mono (\<lambda> pinterp. ?sat_set pinterp body)")
  (* proof
  fix x y :: "'v pred_interp"
  assume "x \<le> y"
  show "?sat_set x body \<subseteq> ?sat_set y body" *)
    (* proof (induction body)
      case (Atomic x)
      then show ?case sorry
    next
      case (Imp x1a body)
      then show ?case try
    next
      case (CondAssert x1a body1 body2)
      then show ?case try
    next
      case (ImpureAnd body1 body2)
      then show ?case try
    next
      case (ImpureOr body1 body2)
      then show ?case try
    next
      case (Star body1 body2)
      then show ?case try
    next
      case (Wand body1 body2)
      then show ?case try
    next
      case (ForAll x1a body)
      then show ?case try
    next
      case (Exists x1a body)
      then show ?case try
    qed
  qed *)
  sorry

section \<open>Complete Lattice of Partial Functions\<close>

text \<open>We want to define a complete lattice for partial functions with a complete lattice as codomain.
HOL already includes \<open>complete_lattice\<close> instantiation for total functions to a complete lattice.
It only remains to instantiate \<open>option\<close> as a complete lattice since \<open>\<rightharpoonup>\<close> is just a type synonym for \<open>'a \<rightarrow> 'b option\<close>.\<close>

instantiation option :: (complete_lattice) complete_lattice
begin
  definition bot_option :: "'a option" where
    "bot_option = None"

  definition top_option  :: "'a option" where
    "top_option = Some top"

  definition Inf_option :: "'a option set \<Rightarrow> 'a option" where
    "Inf_option A = (if None \<in> A then None else Some (Inf {x. Some x \<in> A}))"

  definition Sup_option :: "'a option set \<Rightarrow> 'a option" where
    "Sup_option A = (if \<exists>x. Some x \<in> A then Some (Sup {x. Some x \<in> A}) else None)"

  definition inf_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
    "inf_option x y = Inf {x,y}"

 definition sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option " where
    "sup_option x y = Sup {x,y}"



  lemma Inf_option_lower:
    assumes "x \<in> (A :: 'a option set)"
    shows "Inf A \<le> x"
  proof (cases "x = None")
  case True
    thus ?thesis using assms by (auto simp add:Inf_option_def less_eq_option_def)
  next
  case False
    thus ?thesis using assms by (auto simp add:Inf_option_def less_eq_option_def Inf_lower)
  qed

  lemma Sup_option_upper:
    assumes "x \<in> (A :: 'a option set)"
    shows "x \<le> Sup A"
    proof (cases "x = None")
    case True
      thus ?thesis by (auto simp add:less_eq_option_def)
    next
    case False
      thus ?thesis using assms by (auto simp add:Sup_option_def less_eq_option_def Sup_upper)
    qed

  lemma Inf_option_greatest:
    assumes "\<And>x. x \<in> (A :: 'a option set) \<Longrightarrow> z \<le> x"
    shows "z \<le> Inf A"
    proof (cases "z = None")
    case True
      thus ?thesis by (auto simp add:less_eq_option_def)
    next
    case False
      then obtain w where "z = Some w" by auto
      thus ?thesis using assms by (auto simp add:Inf_option_def less_eq_option_def intro:Inf_greatest)
    qed

    lemma Sup_option_least:
    assumes "\<And>x. x \<in> (A :: 'a option set) \<Longrightarrow> x \<le> z"
    shows "Sup A \<le> z"
    proof (cases "\<forall>y \<in> A. y = None")
    case True
      thus ?thesis by (auto simp add:Sup_option_def less_eq_option_def)
    next
    case False
      then obtain w where "z = Some w" using assms less_eq_option_def by blast
      thus ?thesis using assms by (auto simp add:Sup_option_def less_eq_option_def intro:Sup_least)
    qed


instance proof
  fix x y :: "'a option"
  show "inf x y \<le> x"
    using inf_option_def Inf_option_lower by auto
  show "inf x y \<le> y"
    using inf_option_def Inf_option_lower by auto
  show "x \<le> sup x y"
    using sup_option_def Sup_option_upper by auto
  show "y \<le> sup x y"
    using sup_option_def Sup_option_upper by auto
next
  fix x y z :: "'a option"
  assume "x \<le> y"
     and "x \<le> z"
  thus "x \<le> inf y z"
    using inf_option_def Inf_option_greatest by fastforce
next
  fix y x z :: "'a option"
  assume "y \<le> x"
     and "z \<le> x"
  then show "sup y z \<le> x"
    using sup_option_def Sup_option_least by fastforce
next
  fix x :: "'a option"
  fix A :: "'a option set"
  assume "x \<in> A"
  show "Inf A \<le> x" by (rule Inf_option_lower, fact)
  show "x \<le> Sup A" by (rule Sup_option_upper, fact)
next
  fix A :: "'a option set"
  fix z :: "'a option"
  assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  then show "z \<le> Inf A" using Inf_option_greatest by (auto)
next
  fix A :: "'a option set"
  fix z :: "'a option"
  assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  then show "Sup A \<le> z" using Sup_option_least by (auto)
next
  show "Inf {} = (top :: 'a option)"
    by (simp add: Inf_option_def top_option_def)
next
  show "Sup {} = (bot :: 'a option)"
    by (simp add: Sup_option_def bot_option_def)
qed
end


section \<open>Predicate Interpretation is a complete lattice\<close>

type_synonym 'v pred_interp = "'v predicate_loc \<rightharpoonup> 'v virtual_state set"

lemma pred_interp_is_complete_lattice: "OFCLASS('v pred_interp, complete_lattice_class)" by standard

section \<open>Predicate evaluation\<close>

text \<open>We define a evaluation operation that takes a domain and function interpretation, predicate code definition \<open>predicate_decl\<close>, a predicate interpretation \<open>pred_interp\<close>.
It then uses \<open>sat_set\<close> to evaluate each predicates body against the current interpretation returning an updated predicate interpretation.\<close>

type_synonym 'v domain_interp = "'v \<Rightarrow> abs_type"
type_synonym ('a, 'v) fun_interp = "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'a \<rightharpoonup> 'v val"
type_synonym pred_defs = "predicate_ident \<rightharpoonup> predicate_decl"

(* QUESTION: Difference between {} and None for predicate interpretations? *)

(* Returns the syntactical predicate body for a predicate (permission) location *)
fun pred_body :: "pred_defs \<Rightarrow> 'v domain_interp \<Rightarrow>'v predicate_loc \<rightharpoonup> assertion" where
  "pred_body pdefs D (ident, vargs) = Option.bind (pdefs ident) (\<lambda> decl.
    if vals_well_typed D vargs (predicate_decl.args decl) then predicate_decl.body decl else None )"

section \<open>Least Fixed Point of Predicate Evaluation\<close>

text \<open>To define a predicates semantics as the least fixed point (lfp) of above predicate
evaluation operation, we can apply the Knaster-Tarski theorem which needs the interpretations to form
a complete lattice and the evaluation operation to be monotone.\<close>

context
  fixes dinterp :: "'v domain_interp"
    and finterp :: "('v virtual_state, 'v) fun_interp"
    and F :: "field_name \<rightharpoonup> vtyp"
    and pdefs :: "pred_defs"
begin

(* Evaluates each predicate body given a predicate interpretation and returns the updated predicate interpretation. *)
fun pred_eval :: "'v pred_interp \<Rightarrow> 'v pred_interp" where
  "pred_eval pinterp ploc = Option.bind (pred_body pdefs dinterp ploc) (\<lambda> body.
    Some {get_state \<sigma> | \<sigma>. \<sigma> \<in>
      (\<langle> \<lparr> domains = dinterp, predicates = pinterp, funs = finterp \<rparr> , F\<rangle> \<Turnstile> \<langle>body\<rangle>)
      \<and> get_store \<sigma> = shift_and_add_list_alt Map.empty (snd ploc)
      \<and> get_trace \<sigma> = Map.empty
    } )"

(* EquiSemantics for predicates
this defines a predicate interpretation from syntactic predicate definitions *)
definition pred_sem :: "'v pred_interp" where
  "pred_sem = lfp pred_eval"

lemma pred_eval_mono:
  shows "mono pred_eval"
  (* proof (rule monoI)
    fix x y :: "'v pred_interp"
    assume "x \<le> y"
    show ?thesis[unfolded mono_def]
    proof *)
  unfolding mono_def
  apply (auto simp add: le_fun_def less_eq_option_def split: bind_split)
  apply (auto simp add: get_store_def get_state_def get_trace_def)
  apply (rule_tac x=aa in exI, rule_tac x=ab in exI)
  apply (auto)
  subgoal premises prems for x y
  proof -
    have "x \<le> y" using prems less_eq_option_def by (metis le_funI surj_pair)
    thus ?thesis using prems sat_set_mono[unfolded mono_def] by fast
  qed
  done



(*
proof (rule monoI)
  fix x y :: "'v pred_interp"
  assume "x \<le> y"
  show "pred_eval x \<le> pred_eval y"
  proof (rule le_funI)
    fix ploc :: "'v predicate_loc"
    show "pred_eval x ploc \<le> pred_eval y ploc"
    proof (cases "pred_body pdefs dinterp ploc")
      case None
      then show ?thesis by (simp add: less_eq_option_def)
    next
      case (Some body)
      have "\<langle> \<lparr> domains = dinterp, predicates = x, funs = finterp \<rparr>, F\<rangle> \<Turnstile> \<langle>body\<rangle>
          \<subseteq> \<langle> \<lparr> domains = dinterp, predicates = y, funs = finterp \<rparr>, F\<rangle> \<Turnstile> \<langle>body\<rangle>"
        using sat_set_mono[unfolded mono_def] \<open>x \<le> y\<close> by blast
      with Some show ?thesis
        by (auto simp add: less_eq_option_def)
    qed
  qed
qed
 *)

(*
proof -
 fix x :: "char list \<times> 'v val list \<Rightarrow> 'v virtual_state set option" and y :: "char list \<times> 'v val list \<Rightarrow> 'v virtual_state set option" and a :: "char list" and b :: "'v val list" and v :: predicate_decl and va :: "(pure_exp, pure_exp atomic_assert) assert" and aa :: "(nat \<Rightarrow> 'v val option) agreement" and ab :: "(char list \<Rightarrow> 'v virtual_state option) agreement" and ba :: "'v virtual_state"
 assume a1: "\<forall>a b. x (a, b) = None \<or> (\<exists>v1. x (a, b) = Some v1 \<and> (\<exists>v2. y (a, b) = Some v2 \<and> v1 \<subseteq> v2))"
 assume a2: "(aa, ab, ba) \<in> \<langle>\<lparr>interp.domains = dinterp, predicates = x, funs = finterp\<rparr>, F\<rangle> \<Turnstile> \<langle>va\<rangle>"
 have "x \<le> y"
 using a1 by (metis (no_types) le_funI less_eq_option_def surj_pair)
 then show "(aa, ab, ba) \<in> \<langle>\<lparr>interp.domains = dinterp, predicates = y, funs = finterp\<rparr>, F\<rangle> \<Turnstile> \<langle>va\<rangle>"
 using a2 \<open>\<And>body. \<forall>x y. x \<le> y \<longrightarrow> \<langle>\<lparr>interp.domains = dinterp, predicates = x, funs = finterp\<rparr>, F\<rangle> \<Turnstile> \<langle>body\<rangle> \<subseteq> \<langle>\<lparr>interp.domains = dinterp, predicates = y, funs = finterp\<rparr>, F\<rangle> \<Turnstile> \<langle>body\<rangle>\<close> by auto
qed *)


lemma pred_sem_fp:
  shows "pred_eval pred_sem = pred_sem"
  using lfp_fixpoint pred_eval_mono by (metis pred_sem_def)

definition is_lfp :: "('a ::complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
 "is_lfp f x \<equiv> (f x = x) \<and> (\<forall>y. (f y = y) \<longrightarrow> x \<le> y )"

(* TODO: update to new definition *)
lemma pred_sem_is_lfp:
  shows "is_lfp pred_eval pred_sem"
  proof -
    have "Inf {u. pred_eval u \<le> u} \<le> Inf {u. pred_eval u = u}" by (simp add: Collect_mono_iff Inf_superset_mono)
    hence "pred_sem \<le> Inf {u. pred_eval u = u}" unfolding pred_sem_def lfp_def by auto
    moreover have "Inf {u. pred_eval u = u} \<le> pred_sem" using pred_sem_fp by (simp add: Inf_lower)
    ultimately have "pred_sem = Inf {u. pred_eval u = u}" by auto
    thus ?thesis unfolding is_lfp_def using pred_sem_fp by (auto simp add: Inf_lower)
  qed

(* TODO: define syntactic well-formed predicate bodies
- no wands
- no old
- only defined predicates
- no exists and forall *)


end