theory FixedPointEquiSem
  imports Main ViperAbstract.Instantiation ViperCommon.ViperLang ViperCommon.SepAlgebra
begin

(* TODO:
3. Prove the predicate interpretation is monotone
4. conclude the lfp existence
5. Update the verifies proof in abstractrefinestotal to assume that the interp is the lsp of the predicates in the code
*)
(* TODO Explanation of theory file *)


section \<open>Complete Lattice for Predicate Interpretations\<close>

text \<open>For predicate interpretations \<langle> pred_interp \<rangle> to be a complete lattice, we need to show
that partial functions with a complete lattice as codomain form a complete lattice.
Then Isabelle can infer membership of the complete lattice type class automatically.
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


text \<open>Predicate Interpretation is a complete lattice\<close>

type_synonym 'v pred_interp = "'v predicate_loc \<rightharpoonup> 'v virtual_state set"

lemma pred_interp_is_complete_lattice: "OFCLASS('v pred_interp, complete_lattice_class)" by standard


section \<open>Predicate evaluation\<close>

text \<open>We define a evaluation operation that takes a domain and function interpretation, predicate code definition \<open>predicate_decl\<close>, a predicate interpretation \<open>pred_interp\<close>.
It then uses \<open>sat_set\<close> to evaluate each predicates body against the current interpretation returning an updated predicate interpretation.\<close>

type_synonym assertion = "ViperLang.assertion"
type_synonym 'v domain_interp = "'v \<Rightarrow> abs_type"
type_synonym ('a, 'v) fun_interp = "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'a \<rightharpoonup> 'v val"
type_synonym pred_defs = "predicate_ident \<rightharpoonup> predicate_decl"

(* QUESTION: Difference between {} and None for predicate interpretations? *)
(* ANSWER: The difference might lie in the definition of the acc assertion *)

(* Returns the syntactical predicate body for a predicate (permission) location *)
fun pred_body :: "pred_defs \<Rightarrow> 'v domain_interp \<Rightarrow>'v predicate_loc \<rightharpoonup> assertion" where
  "pred_body pdefs D (ident, vargs) = Option.bind (pdefs ident) (\<lambda> decl.
    if vals_well_typed D vargs (predicate_decl.args decl) then predicate_decl.body decl else None )"

section \<open>Restrict predicates by some defintion of well-formedness\<close>

text \<open>We restrict ourselves to assertions without wands\<close>

definition no_wand_forall_exists_assertion :: "assertion \<Rightarrow> bool" where
  "no_wand_forall_exists_assertion A \<longleftrightarrow> assert_pred
      (\<lambda> a. case a of Wand _ _ \<Rightarrow> False | ForAll _ _ \<Rightarrow> False | Exists _ _ \<Rightarrow> False | _ \<Rightarrow> True) (\<lambda>_. True) (\<lambda>_. True) A"

(* TODO exclude Forall and Exists *)
definition wf_pred_body :: "assertion \<Rightarrow> bool" where
  "wf_pred_body A \<longleftrightarrow> no_wand_forall_exists_assertion A"

definition wf_pred :: "predicate_decl \<Rightarrow> bool" where
  "wf_pred p \<longleftrightarrow> (case predicate_decl.body p of None \<Rightarrow> False | Some b \<Rightarrow> wf_pred_body b)"

definition wf_pred_defs :: "pred_defs \<Rightarrow> bool" where
  "wf_pred_defs pdefs \<longleftrightarrow> (\<forall>p. p \<in> dom pdefs \<longrightarrow> wf_pred (the (pdefs p)))"

text \<open>Well-formedness of an assertion carries over to its sub-assertions (needed for the induction hypotheses).\<close>

lemma wf_pred_body_sub:
  "\<not> wf_pred_body (Wand A B)"
  "\<not> wf_pred_body (ForAll ty A)"
  "\<not> wf_pred_body (Exists ty A)"
  "wf_pred_body (Star A B) \<Longrightarrow> wf_pred_body A \<and> wf_pred_body B"
  "wf_pred_body (ImpureAnd A B) \<Longrightarrow> wf_pred_body A \<and> wf_pred_body B"
  "wf_pred_body (ImpureOr A B) \<Longrightarrow> wf_pred_body A \<and> wf_pred_body B"
  "wf_pred_body (CondAssert e A B) \<Longrightarrow> wf_pred_body A \<and> wf_pred_body B"
  "wf_pred_body (Imp e A) \<Longrightarrow> wf_pred_body A"
  by (simp_all add: wf_pred_body_def no_wand_forall_exists_assertion_def)

section \<open>Monotony of Satisfiability\<close>

text \<open>To later show that the predicate evaluation operation is monotone,
we show helper lemmas in this section to establish monotony for subfunctions that
revolve around which states an assertion satisfies.\<close>


context
  fixes dinterp :: "'v domain_interp"
    and finterp :: "('v virtual_state, 'v) fun_interp"
    and F :: "field_name \<rightharpoonup> vtyp"
    and pdefs :: "pred_defs"
begin

abbreviation mk_interp :: "'v pred_interp \<Rightarrow> ('v, 'v virtual_state) interp" where
  "mk_interp pinterp \<equiv> \<lparr> domains = dinterp, predicates = pinterp, funs = finterp \<rparr>"

lemma red_pure_assert_const:
  fixes e :: "pure_exp"
    and r :: "'v extended_val"
  shows "let pa = (\<lambda>pinterp. mk_interp pinterp \<turnstile> \<langle>e\<rangle> [\<Down>] r) in pa pinterp = pa pinterp'"
  unfolding  red_pure_assert_def corely_def
  using red_pure_indep_interp_pred
  by (smt (verit) Collect_cong interp.select_convs(1,3) subsetI)


lemma atomic_assert_mono:
  fixes A :: "pure_exp atomic_assert"
  shows "mono (\<lambda> pinterp. atomic_assert (mk_interp pinterp) F A (Some True))" (is "mono (\<lambda> pinterp. ?atomic_assert pinterp A)")
  proof
    fix x y :: "'v pred_interp"
    note red_pure_xy = red_pure_assert_const[unfolded Let_def, where pinterp = x and pinterp' = y]
    assume "x \<le> y"
    then show "?atomic_assert x A \<le> ?atomic_assert y A"
    proof (cases A)
      case (Pure e)
      then show ?thesis by (auto simp add: red_pure_xy)
    next
        case (Acc e f w)
        then show ?thesis using \<open>x\<le>y\<close>
        apply (auto del: subsetI intro!: SUP_subset_mono[OF subset_refl] add_set_mono simp add: red_pure_xy split: exp_or_wildcard.split)
        (* TODO acc_mono *)
        sorry
      next
        case (AccPredicate name args w)
        then show ?thesis using \<open>x\<le>y\<close>
        apply (auto del: subsetI intro!: SUP_subset_mono[OF subset_refl] add_set_mono simp add: red_pure_xy split: exp_or_wildcard.split)
        (* TODO acc_pred_mono *)
        sorry
      qed
    qed

lemma sat_set_mono:
  fixes body :: "assertion"
  assumes "wf_pred_body body"
  shows "mono (\<lambda> pinterp. \<langle> mk_interp pinterp, F \<rangle> \<Turnstile> \<langle>body\<rangle> )" (is "mono (\<lambda> pinterp. ?sat_set pinterp body)")
  proof
    fix x y :: "'v pred_interp"
    note red_pure_xy = red_pure_assert_const[unfolded Let_def, where pinterp = x and pinterp' = y]
    assume "x \<le> y"
    then show "?sat_set x body \<le> ?sat_set y body"
      using assms
    proof (induction body)
      case (Atomic a)
      show ?case using monoD[OF atomic_assert_mono \<open>x \<le> y\<close>] by simp
    next
      case (Imp e A)
      hence "?sat_set x A \<le> ?sat_set y A" using wf_pred_body_sub by blast
      thus ?case
      unfolding sat_set.simps
      by (intro SUP_subset_mono[OF subset_refl] add_set_mono)
        (auto simp add: red_pure_xy)
    next
      case (CondAssert e A B)
      hence "?sat_set x A \<le> ?sat_set y A" "?sat_set x B \<le> ?sat_set y B"
        using wf_pred_body_sub by blast+
      thus ?case
      unfolding sat_set.simps
      by (intro SUP_subset_mono[OF subset_refl] add_set_mono)
        (auto simp add: red_pure_xy)
    next
      case (ImpureAnd A B)
      hence "?sat_set x A \<le> ?sat_set y A" "?sat_set x B \<le> ?sat_set y B"
        using wf_pred_body_sub by blast+
      thus ?case by auto
    next
      case (ImpureOr A B)
      hence "?sat_set x A \<le> ?sat_set y A" "?sat_set x B \<le> ?sat_set y B"
        using wf_pred_body_sub by blast+
      thus ?case by auto
    next
      case (Star A B)
      hence "?sat_set x A \<le> ?sat_set y A" "?sat_set x B \<le> ?sat_set y B"
        using wf_pred_body_sub by blast+
      thus ?case using assms wf_pred_body_sub add_set_mono by (metis sat_set.simps(4))
    (* remaining cases Wand, ForAll, Exists are trivial as they are not allowed in predicate bodies *)
    qed (use wf_pred_body_sub in blast)+
  qed


section \<open>Least Fixed Point of Predicate Evaluation\<close>

text \<open>To define a predicates semantics as the least fixed point (lfp) of above predicate
evaluation operation, we can apply the Knaster-Tarski theorem which needs the interpretations to form
a complete lattice and the evaluation operation to be monotone.\<close>



(* Evaluates each predicate body given a predicate interpretation and returns the updated predicate interpretation. *)
fun pred_eval :: "'v pred_interp \<Rightarrow> 'v pred_interp" where
  "pred_eval pinterp ploc = Option.bind (pred_body pdefs dinterp ploc) (\<lambda> body.
    Some {get_state \<sigma> | \<sigma>. \<sigma> \<in>
      (\<langle> mk_interp pinterp, F\<rangle> \<Turnstile> \<langle>body\<rangle>)
      \<and> get_store \<sigma> = shift_and_add_list_alt Map.empty (snd ploc)
      \<and> get_trace \<sigma> = Map.empty
    } )"

(* EquiSemantics for predicates
this defines a predicate interpretation from syntactic predicate definitions *)
definition pred_sem :: "'v pred_interp" where
  "pred_sem = lfp pred_eval"

(* TODO *)
lemma pred_eval_mono:
  assumes wf: "wf_pred_defs pdefs"
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
  subgoal premises prems for x y _ _ _ pb
  proof -
    have "x \<le> y" using prems less_eq_option_def by (metis le_funI surj_pair)
    moreover have "wf_pred_body pb" using wf wf_pred_body_sub wf_pred_defs_def wf_pred_def by (metis domI option.sel option.simps(5) prems(2,4))
    ultimately show ?thesis using prems sat_set_mono[unfolded mono_def] wf pred_body.simps by fast
  qed
  done


lemma pred_sem_fp:
  assumes wf: "wf_pred_defs pdefs"
  shows "pred_eval pred_sem = pred_sem"
  using lfp_fixpoint pred_eval_mono assms by (metis pred_sem_def)

definition is_lfp :: "('a ::complete_lattice \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
 "is_lfp f x \<equiv> (f x = x) \<and> (\<forall>y. (f y = y) \<longrightarrow> x \<le> y )"

lemma pred_sem_is_lfp:
  assumes wf: "wf_pred_defs pdefs"
  shows "is_lfp pred_eval pred_sem"
  proof -
    have "Inf {u. pred_eval u \<le> u} \<le> Inf {u. pred_eval u = u}" by (simp add: Collect_mono_iff Inf_superset_mono)
    hence "pred_sem \<le> Inf {u. pred_eval u = u}" unfolding pred_sem_def lfp_def by auto
    moreover have "Inf {u. pred_eval u = u} \<le> pred_sem" using pred_sem_fp wf by (simp add: Inf_lower)
    ultimately have "pred_sem = Inf {u. pred_eval u = u}" by auto
    thus ?thesis unfolding is_lfp_def using pred_sem_fp wf by (auto simp add: Inf_lower)
  qed

(* QUESTION:
These don't seem to be necessary to exclude:
- no old
- only defined predicates
*)


end