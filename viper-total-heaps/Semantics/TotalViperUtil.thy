section \<open>Utility functions and lemmas for Viper\<close>

theory TotalViperUtil
imports ViperCommon.ValueAndBasicState ViperCommon.DeBruijn ViperCommon.ViperUtil ViperCommon.PosReal TotalUtil
begin

fun get_address_opt :: "'a val \<Rightarrow> address option"
  where
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"

fun f_None :: "'a \<Rightarrow> 'b option"
  where "f_None _ = None"

subsection \<open>Positive rationals (TODO: move to Viper theory?)\<close>

lemma prat_non_negative: "\<And>q. Rep_preal q \<ge> 0"
  by (transfer) simp

lemma psub_smaller:
  assumes "(p :: preal) \<ge> q"
  shows "p \<ge> (p - q)"
  unfolding minus_preal_def
proof -
  from assms have DiffNonNegative: "Rep_preal p - Rep_preal q \<ge> 0"
    by (transfer) simp

  have "Rep_preal p \<ge> Rep_preal p - Rep_preal q"
    by (transfer) simp


  hence "(Rep_preal p) \<ge> Rep_preal (Abs_preal (Rep_preal p - Rep_preal q))"
    using Abs_preal_inverse DiffNonNegative
    by fastforce

  thus "map_fun id (map_fun id Abs_preal) (\<lambda>a b. if b \<le> a then Rep_preal a - Rep_preal b else 0) p q \<le> p"
    using assms less_eq_preal.rep_eq minus_preal.abs_eq by auto
qed

subsection \<open>Recursive predicates on assertions\<close>

(* The general predicates \<open>pure_exp_pred\<close>, \<open>atomic_assert_pred\<close>, \<open>assert_pred\<close>, and
\<open>stmt_pred\<close> are defined in \<open>ViperLang\<close> *)

subsubsection \<open>Common instantiations\<close>

text \<open>No permission introspection\<close>

fun no_perm_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "no_perm_pure_exp_no_rec (Perm e f) = False"
  | "no_perm_pure_exp_no_rec (PermPred e f) = False"
  | "no_perm_pure_exp_no_rec _ = True"

abbreviation no_perm_pure_exp
  where "no_perm_pure_exp \<equiv> pure_exp_pred no_perm_pure_exp_no_rec"

abbreviation no_perm_assertion
  where "no_perm_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_perm_pure_exp_no_rec"

text \<open>No old expressions\<close>

fun no_old_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "no_old_pure_exp_no_rec (Old _ _) = False"
  | "no_old_pure_exp_no_rec _ = True"

abbreviation no_old_pure_exp
  where "no_old_pure_exp \<equiv> pure_exp_pred no_old_pure_exp_no_rec"

abbreviation no_old_assertion
  where "no_old_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_old_pure_exp_no_rec"

abbreviation no_old_stmt
  where "no_old_stmt \<equiv> stmt_pred (\<lambda>_. True) no_old_assertion no_old_pure_exp"

text \<open>parts not supported by proof generation\<close>

fun no_unfolding_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "no_unfolding_pure_exp_no_rec (Unfolding p es e) = False"
  | "no_unfolding_pure_exp_no_rec _ = True"

abbreviation no_unfolding_pure_exp
  where "no_unfolding_pure_exp \<equiv> pure_exp_pred no_unfolding_pure_exp_no_rec"

abbreviation no_unfolding_assertion
  where "no_unfolding_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_unfolding_pure_exp_no_rec"

fun not_supported_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "not_supported_exp_no_rec (Unfolding p es e) = False"
  | "not_supported_exp_no_rec Result = False"
  | "not_supported_exp_no_rec _ = True"

abbreviation supported_pure_exp
  where "supported_pure_exp \<equiv> pure_exp_pred not_supported_exp_no_rec"

fun supported_atomic_assert :: "pure_exp atomic_assert \<Rightarrow> bool"
  where
    "supported_atomic_assert (Acc e f Wildcard) = False" \<comment>\<open>wildcard permission amounts not supported\<close>
  | "supported_atomic_assert (AccPredicate pred es q) = False" \<comment>\<open>predicates not supported\<close>
  | "supported_atomic_assert _ = True"

abbreviation supported_assertion
  where "supported_assertion \<equiv> assert_pred (\<lambda>_. True) supported_atomic_assert not_supported_exp_no_rec"

lemma supported_pure_exp_no_unfolding:
  assumes "supported_pure_exp e"
  shows "no_unfolding_pure_exp e"
  using assms
  apply (induction e)
                 apply simp_all
  using list.pred_mono_strong
    apply (force, force)
  using pure_exp_pred.elims(3)
  by fastforce

lemma supported_assertion_no_unfolding:
  assumes "supported_assertion A"
  shows "no_unfolding_assertion A"
  using assms
  apply (induction A)
          apply (simp_all add: supported_pure_exp_no_unfolding)
  by (metis atomic_assert_pred.elims(2) atomic_assert_pred.elims(3) atomic_assert_pred_rec.elims(3) atomic_assert_pred_rec.simps(1) atomic_assert_pred_rec.simps(3) supported_atomic_assert.simps(1) supported_atomic_assert.simps(2) supported_pure_exp_no_unfolding)


subsubsection \<open>No result expressions\<close>

fun no_result_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "no_result_pure_exp_no_rec Result = False"
  | "no_result_pure_exp_no_rec _ = True"

abbreviation no_result_pure_exp
  where "no_result_pure_exp \<equiv> pure_exp_pred no_result_pure_exp_no_rec"

abbreviation no_result_assertion
  where "no_result_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_result_pure_exp_no_rec"


subsubsection \<open>supported predicate body\<close>

abbreviation supported_pred_expr
  where "supported_pred_expr e \<equiv> no_perm_pure_exp e \<and> no_old_pure_exp e \<and> no_result_pure_exp e"

abbreviation supported_pred_body
  where "supported_pred_body A \<equiv> no_perm_assertion A \<and> no_old_assertion A \<and> no_result_assertion A"


subsection \<open>Free variables\<close>

fun free_var_pure_exp :: "pure_exp \<Rightarrow> var set"
  where
  "free_var_pure_exp (Var x) = {x}"
| "free_var_pure_exp (ELit lit) = {}"
| "free_var_pure_exp Result = {}"
| "free_var_pure_exp (Unop uop e) = free_var_pure_exp e"
| "free_var_pure_exp (Binop e1 bop e2) = free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_pure_exp (CondExp cond e1 e2) = free_var_pure_exp cond \<union> free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_pure_exp (FieldAcc e f) = free_var_pure_exp e"
| "free_var_pure_exp (Old lbl e) = free_var_pure_exp e"
| "free_var_pure_exp (Perm e f) = free_var_pure_exp e"
| "free_var_pure_exp (PermPred pname es) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_pure_exp (FunApp f es) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_pure_exp (Unfolding pname es e) = \<Union> (set (map free_var_pure_exp es)) \<union> free_var_pure_exp e"
| "free_var_pure_exp (pure_exp.Let e e_body) = free_var_pure_exp e \<union> (shift_down_set (free_var_pure_exp e_body))"
| "free_var_pure_exp (PExists ty e) = shift_down_set (free_var_pure_exp e)"
| "free_var_pure_exp (PForall ty e) = shift_down_set (free_var_pure_exp e)"
| "free_var_pure_exp DummyExpr = {}"

fun
  free_var_atomic_assert :: "pure_exp atomic_assert \<Rightarrow> var set" where
  "free_var_atomic_assert (Pure e) = free_var_pure_exp e"
| "free_var_atomic_assert (Acc e f Wildcard) = free_var_pure_exp e"
| "free_var_atomic_assert (Acc e1 f (PureExp e2)) = free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_atomic_assert (AccPredicate pname es Wildcard) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_atomic_assert (AccPredicate pname es (PureExp e2)) = \<Union> (set (map free_var_pure_exp es)) \<union> free_var_pure_exp e2"

fun free_var_assertion :: "assertion \<Rightarrow> var set"  where
  "free_var_assertion (Atomic atm) = free_var_atomic_assert atm"
| "free_var_assertion (Imp e A) = free_var_pure_exp e \<union> free_var_assertion A"
| "free_var_assertion (CondAssert e A B) = free_var_pure_exp e \<union> free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (A && B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ImpureAnd A B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ImpureOr A B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ForAll _ A) = free_var_assertion A"
| "free_var_assertion (Exists _ A) = free_var_assertion A"
| "free_var_assertion (Wand A B) = free_var_assertion A \<union> free_var_assertion B"

end