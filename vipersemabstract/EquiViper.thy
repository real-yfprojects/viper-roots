theory EquiViper
  imports Main ViperCommon.PosPerm ViperCommon.ValueAndBasicState ViperCommon.PartialMap ViperCommon.Binop ViperCommon.DeBruijn
    ViperCommon.PosReal ViperCommon.SepAlgebra AbstractSemantics
begin

subsection \<open>Pre-virtual equi_states\<close>

type_synonym 'a pre_virtual_state = "preal mask \<times> 'a partial_heap"

instantiation val :: (type) pcm
begin

definition plus_val :: "'a val \<Rightarrow> 'a val \<Rightarrow> 'a val option" where
  "plus_val a b = (if a = b then Some a else None)"

instance proof
  fix a b c ab bc :: "'a val"
  show "a \<oplus> b = b \<oplus> a"
    using plus_val_def by presburger
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (metis option.sel plus_val_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (metis option.sel plus_val_def)
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a "
    by (metis plus_val_def)
qed

end

lemma plus_val_id :
  "(v :: 'a val) \<oplus> v = Some v"
  by (simp add: plus_val_def)

lemma defined_val :
  "(v :: 'a val) ## v' \<longleftrightarrow> v = v'"
  by (simp add: defined_def plus_val_def)


instantiation val :: (type) pcm_mult
begin

definition mult_val :: "preal \<Rightarrow> 'a val \<Rightarrow> 'a val" where
  "mult_val \<alpha> x = x"

instance proof
  fix x a b :: "'a val"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_val_def)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult_val_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: mult_val_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    by (simp add: mult_val_def plus_val_def)
qed

end

definition wf_permission_occupied :: "'a pre_virtual_state \<Rightarrow> bool" where
  "wf_permission_occupied st \<longleftrightarrow> (\<forall>hl. ppos (fst st hl) \<longrightarrow> snd st hl \<noteq> None)"

definition wf_pre_virtual_state :: "'a pre_virtual_state \<Rightarrow> bool" where
  "wf_pre_virtual_state st \<longleftrightarrow> wf_permission_occupied st \<and> wf_mask_simple (fst st)"


lemma wf_pre_virtual_stateI:
  assumes "\<And>hl. ppos (\<pi> hl) \<Longrightarrow> h hl \<noteq> None"
  assumes "wf_mask_simple \<pi>"
  shows "wf_pre_virtual_state (\<pi>, h)"
  using assms by (simp add:wf_pre_virtual_state_def wf_permission_occupied_def)


subsection \<open>Additions\<close>

lemma masks_can_always_be_added:
  "(a :: preal mask) ## b"
  by (simp add: compatible_fun_def defined_def plus_fun_def plus_preal_def)

lemma add_masks_def:
  assumes "Some (\<pi>:: preal mask) = \<pi>1 \<oplus> \<pi>2"
  shows "\<pi> hl = \<pi>1 hl + \<pi>2 hl"
  using assms plus_funE plus_preal_def by fastforce

text \<open>Two equi_states can be added iff their heaps are compatible\<close>

lemma pre_wf_plus_def:
  "(\<pi>' :: preal mask, h') ## (\<pi>, h) \<longleftrightarrow> h' ## h"
  by (simp add: comp_prod masks_can_always_be_added)

subsection \<open>Empty state\<close>



subsection \<open>Unbounded virtual equi_states\<close>

text \<open>These are derived from pre_virtual_state and form the basis of the virtual state.
  To implement recursive predicate semantics we need to allow states with more than
  1 permission to satisfy predicates such that fractional predicate permissions
  can be handled correctly.\<close>

definition empty_heap :: "'a partial_heap" where "empty_heap = Map.empty"
definition uuu :: "'a pre_virtual_state" where "uuu = (zero_mask, empty_heap)"

lemma wf_uuu:
  "wf_pre_virtual_state (zero_mask, empty_heap)"
proof (rule wf_pre_virtual_stateI)
  show "\<And>hl. ppos (zero_mask hl) \<Longrightarrow> empty_heap hl \<noteq> None"
    by (simp add: ppos.rep_eq zero_mask_def zero_preal.rep_eq)
  show "wf_mask_simple (zero_mask)"
    by (simp add: wf_zero_mask)
qed

typedef 'a unbounded_virtual_state = "{ \<phi> :: 'a pre_virtual_state |\<phi>. wf_permission_occupied \<phi> }"
  using wf_uuu wf_pre_virtual_state_def by blast

setup_lifting type_definition_unbounded_virtual_state


lift_definition unuu :: "'a unbounded_virtual_state" is "uuu"
  using wf_uuu by (auto simp add: uuu_def wf_pre_virtual_state_def)

definition is_bounded :: "  'a unbounded_virtual_state \<Rightarrow> bool" where
  "is_bounded \<phi> = wf_mask_simple (fst (Rep_unbounded_virtual_state \<phi>))"


lift_definition get_uvh :: "'a unbounded_virtual_state \<Rightarrow> 'a partial_heap" is "snd" .
definition get_uvm :: "'a unbounded_virtual_state \<Rightarrow> preal mask" where "get_uvm \<phi> = fst (Rep_unbounded_virtual_state \<phi>)"

instantiation unbounded_virtual_state :: (type) pcm
begin

lift_definition plus_unbounded_virtual_state :: "'a unbounded_virtual_state \<Rightarrow> 'a unbounded_virtual_state \<Rightarrow> 'a unbounded_virtual_state option"
  is "plus"
  apply ( simp add: wf_permission_occupied_def pred_option_def Product_Type.split_paired_all del:Product_Type.split_paired_All)
proof clarify
  fix am ah bm bh cm ch hl f
  assume asm0: "\<forall> hl. PosReal.ppos (am hl) \<longrightarrow> (\<exists>y. ah hl = Some y)"
    "\<forall>hl. PosReal.ppos (bm hl) \<longrightarrow> (\<exists>y. bh hl = Some y)"
    "(am, ah) \<oplus> (bm, bh) = Some (cm, ch)" "PosReal.ppos (fst (cm, ch) (hl, f))"
  hence "am (hl, f) > 0 \<or>  bm (hl, f) > 0"
    using plus_prodE preal_plusE
    by (metis (mono_tags, lifting) add.right_neutral fst_conv gr_0_is_ppos plus_funE pperm_pnone_pgt)
  then have "ah (hl, f) \<noteq> None \<or> bh (hl, f) \<noteq> None"
    using asm0(1,2) gr_0_is_ppos by blast
  then have "ch (hl, f) \<noteq> None"
    using plus_prodE asm0(3) plus_funE
    by (smt (verit) asso1 option_plus_None_r plus_option.simps(1) positivity split_pairs)
  then show "\<exists>y. snd (cm, ch) (hl, f) = Some y"
    by auto
qed

lemma compatible_unbounded_virtual_state_implies_pre_virtual_state:
  assumes "Some x = a \<oplus> b"
  shows "Some (Rep_unbounded_virtual_state x) = Rep_unbounded_virtual_state a \<oplus> Rep_unbounded_virtual_state b"
  using assms apply (transfer) by (clarsimp split:bind_splits if_splits)

lemma compatible_unbounded_virtual_state_implies_pre_virtual_state_rev:
  assumes "Some (Rep_unbounded_virtual_state x) = Rep_unbounded_virtual_state a \<oplus> Rep_unbounded_virtual_state b"
  shows "Some x = a \<oplus> b"
  using assms apply (transfer) by (clarsimp  split:bind_splits if_splits)

lemma unbounded_virtual_state_plus_None :
  "a \<oplus> b = None \<longleftrightarrow> Rep_unbounded_virtual_state a \<oplus> Rep_unbounded_virtual_state b = None"
  by (simp add: EquiViper.plus_unbounded_virtual_state_def)

instance proof
  fix a b c ab bc :: "'a unbounded_virtual_state"
  let ?a = "Rep_unbounded_virtual_state a"
  let ?b = "Rep_unbounded_virtual_state b"
  let ?c = "Rep_unbounded_virtual_state c"
  let ?ab = "Rep_unbounded_virtual_state ab"
  let ?bc = "Rep_unbounded_virtual_state bc"

  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative plus_unbounded_virtual_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (smt (verit, del_insts) compatible_unbounded_virtual_state_implies_pre_virtual_state asso1 map_fun_apply plus_unbounded_virtual_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    apply (auto simp add:unbounded_virtual_state_plus_None)
    by (metis asso2 compatible_unbounded_virtual_state_implies_pre_virtual_state)

  assume asm0: "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then show "Some a = a \<oplus> a"
    using compatible_unbounded_virtual_state_implies_pre_virtual_state[of c c c]
      compatible_unbounded_virtual_state_implies_pre_virtual_state[of c a b]
      compatible_unbounded_virtual_state_implies_pre_virtual_state_rev[of a a a]
      positivity[of "Rep_unbounded_virtual_state a" "Rep_unbounded_virtual_state b" "Rep_unbounded_virtual_state c"]
    by fastforce

qed


(* lemma plus_bounded_downward:
  assumes "a \<oplus> b = Some c" "is_bounded a" "is_bounded c"
  shows "is_bounded b"
  using assms plus_prodE[of "Rep_unbounded_virtual_state a" "Rep_unbounded_virtual_state b"]
  apply (auto simp add: unbounded_virtual_state_plus_None compatible_unbounded_virtual_state_implies_pre_virtual_state is_bounded_def)
  apply (auto simp add: is_bounded_def plus_unbounded_virtual_state_def wf_mask_simple_def compatible_unbounded_virtual_state_implies_pre_virtual_state)
*)

end

lemma get_uvh_mono:
  assumes "\<phi>2 \<succeq> \<phi>1"
    and "get_uvh \<phi>1 hl = Some v"
  shows "get_uvh \<phi>2 hl = Some v"
proof -
  obtain \<phi>0 where "Some \<phi>2 = \<phi>1 \<oplus> \<phi>0"
    using assms(1) greater_def by auto
  then have "Some (Rep_unbounded_virtual_state \<phi>2) = Rep_unbounded_virtual_state \<phi>1 \<oplus> Rep_unbounded_virtual_state \<phi>0"
    by (rule compatible_unbounded_virtual_state_implies_pre_virtual_state)
  then have "Rep_unbounded_virtual_state \<phi>2 \<succeq> Rep_unbounded_virtual_state \<phi>1"
    using greater_def by auto
  then have "snd (Rep_unbounded_virtual_state \<phi>2) \<succeq> snd (Rep_unbounded_virtual_state \<phi>1)"
    by (simp add: greater_prod_eq)
  then have "get_uvh \<phi>2 \<succeq> get_uvh \<phi>1"
    by (simp add: get_uvh.rep_eq)
  then have "get_uvh \<phi>2 hl \<succeq> get_uvh \<phi>1 hl"
    by (simp add: greaterE)
  then obtain vo where "Some (get_uvh \<phi>2 hl) = vo \<oplus> Some v"
    using assms(2) greater_equiv by auto
  then show ?thesis
  proof (cases vo)
    case None
    then show ?thesis
      using \<open>Some (get_uvh \<phi>2 hl) = vo \<oplus> Some v\<close> by auto
  next
    case (Some v')
    then obtain v0 where "get_uvh \<phi>2 hl = Some v0" "Some v0 = v' \<oplus> v"
      by (metis (full_types) \<open>Some (get_uvh \<phi>2 hl) = vo \<oplus> Some v\<close> option.distinct(1) option.sel plus_option.simps(3) plus_val_def)
    moreover have "v0 = v"
      by (metis calculation(2) option.discI option.inject plus_val_def)
    ultimately show ?thesis
      by simp
  qed
qed

lemma uvstate_wf_imp:
  "get_uvm \<phi> hl > 0 \<Longrightarrow> get_uvh \<phi> hl \<noteq> None"
  using Rep_unbounded_virtual_state gr_0_is_ppos get_uvh.rep_eq get_uvm_def wf_permission_occupied_def
  by (metis mem_Collect_eq)

lemma uvstate_add_iff:
  "Some (c :: 'v unbounded_virtual_state) = a \<oplus> b \<longleftrightarrow> Some (get_uvh c) = get_uvh a \<oplus> get_uvh b \<and> Some (get_uvm c) = get_uvm a \<oplus> get_uvm b" (is "?FULL \<longleftrightarrow> ?PART")
proof
  assume ?FULL
  then have "Some (Rep_unbounded_virtual_state c) = Rep_unbounded_virtual_state a \<oplus> Rep_unbounded_virtual_state b"
    by (rule compatible_unbounded_virtual_state_implies_pre_virtual_state)
  then show ?PART
    by (metis get_uvh.rep_eq get_uvm_def plus_prodE)
next
  assume ?PART
  then have "Some (Rep_unbounded_virtual_state c) = Rep_unbounded_virtual_state a \<oplus> Rep_unbounded_virtual_state b"
    by (metis get_uvh.rep_eq get_uvm_def plus_prodI prod.collapse)
  then show ?FULL
    by (rule compatible_unbounded_virtual_state_implies_pre_virtual_state_rev)
qed

(* TODO instantiate pcm, pcm_mult and sep_algebra *)

subsection \<open>Virtual equi_states\<close>


typedef 'a virtual_state = "{ \<phi> :: 'a unbounded_virtual_state |\<phi>. is_bounded \<phi> }"
  using wf_uuu is_bounded_def
  by (metis Rep_unbounded_virtual_state_cases mem_Collect_eq wf_pre_virtual_state_def)

setup_lifting type_definition_virtual_state

abbreviation vs2tuple :: "'a virtual_state \<Rightarrow> 'a pre_virtual_state" where
  "vs2tuple \<phi> \<equiv> Rep_unbounded_virtual_state (Rep_virtual_state \<phi>)"

lift_definition get_vh :: "'a virtual_state \<Rightarrow> 'a partial_heap" is "get_uvh" .

lift_definition get_vm :: "'a virtual_state \<Rightarrow> preal mask" is "get_uvm" .

lemma virtual_state_ext:
  assumes "get_vh a = get_vh b"
    and "get_vm a = get_vm b"
  shows "a = b"
  by (metis Rep_unbounded_virtual_state_inverse Rep_virtual_state_inverse assms(1,2) get_vh.rep_eq get_vm.rep_eq get_uvh.rep_eq get_uvm_def prod.exhaust_sel)


lift_definition uu :: "'a virtual_state" is "unuu"
  using wf_uuu
  by (simp add: is_bounded_def unuu.rep_eq uuu_def wf_zero_mask)

lemma uu_get :
  shows "get_vm uu = zero_mask" "get_vh uu = empty_heap"
  by (simp_all add:get_vm.rep_eq get_vh.rep_eq get_uvm_def get_uvh.rep_eq uu.rep_eq uuu_def unuu.rep_eq)



fun read_field :: "'a unbounded_virtual_state \<Rightarrow> heap_loc \<Rightarrow> 'a val option"
  where "read_field \<phi> loc = get_uvh \<phi> loc"

lemma read_field_mono:
  assumes "\<phi>2 \<succeq> \<phi>1"
    and "read_field \<phi>1 hl = Some v"
  shows "read_field \<phi>2 hl = Some v"
  using assms get_uvh_mono by simp

lemma wf_mask_simple_get_vm [simp] :
  "wf_mask_simple (get_vm x)"
  using Rep_virtual_state get_vm.rep_eq get_uvm_def is_bounded_def
  by (metis mem_Collect_eq)

lemma get_vm_bound :
  "get_vm x hl \<le> 1"
  using wf_mask_simple_get_vm wf_mask_simple_def by blast

subsection \<open>Addition of virtual equi_states\<close>


instantiation virtual_state :: (type) pcm
begin


lift_definition plus_virtual_state :: "'a virtual_state \<Rightarrow> 'a virtual_state \<Rightarrow> 'a virtual_state option"
  is "(\<lambda> st1 st2. Option.bind (st1 \<oplus> st2) (\<lambda> x. if is_bounded x then Some x else None))"
  by (simp add: bind_split)

lemma compatible_virtual_state_implies_unbounded_virtual_state:
  assumes "Some x = a \<oplus> b"
  shows "Some (Rep_virtual_state x) = Rep_virtual_state a \<oplus> Rep_virtual_state b"
  using assms apply (transfer) by (clarsimp split:bind_splits if_splits)

lemma compatible_virtual_state_implies_unbounded_virtual_state_rev:
  assumes "Some (Rep_virtual_state x) = Rep_virtual_state a \<oplus> Rep_virtual_state b"
  shows "Some x = a \<oplus> b"
  using assms apply (transfer) by (clarsimp simp add:wf_pre_virtual_state_def split:bind_splits if_splits)


lemma virtual_state_plus_None :
  "a \<oplus> b = None \<longleftrightarrow> Rep_virtual_state a \<oplus> Rep_virtual_state b = None \<or> \<not> wf_mask_simple (the (get_vm a \<oplus> get_vm b))"
proof (cases "Rep_virtual_state a \<oplus> Rep_virtual_state b")
  case None
  then show ?thesis
    by (auto simp add: plus_virtual_state_def)
next
  case (Some c)
  moreover then have "a \<oplus> b = None \<longleftrightarrow> \<not> is_bounded c"
    by (auto simp add: plus_virtual_state_def)
  moreover have "fst (Rep_unbounded_virtual_state c) = the (get_vm a \<oplus> get_vm b)"
    by (simp add: Some compatible_unbounded_virtual_state_implies_pre_virtual_state[of c "Rep_virtual_state a" "Rep_virtual_state b"] get_vm.rep_eq[of b] get_vm.rep_eq[of a] get_uvm_def plus_prodE[of "vs2tuple a" "vs2tuple b" "Rep_unbounded_virtual_state c"])
  ultimately show ?thesis
    by (auto simp add: plus_virtual_state_def is_bounded_def plus_prodE)
qed

lemma plus_masks_the:
  "the ((\<pi>1 :: preal mask) \<oplus> \<pi>2) hl = \<pi>1 hl + \<pi>2 hl"
  by (metis EquiViper.add_masks_def defined_def masks_can_always_be_added option.collapse)

lemma get_vm_plus:
  assumes "a \<oplus> b = Some ab"
  shows "get_vm ab hl = get_vm a hl + get_vm b hl"
proof -
  have "Some (vs2tuple ab) = vs2tuple a \<oplus> vs2tuple b"
    using assms compatible_virtual_state_implies_unbounded_virtual_state
      compatible_unbounded_virtual_state_implies_pre_virtual_state by metis
  then have "Some (get_vm ab) = get_vm a \<oplus> get_vm b"
    by (metis get_vm.rep_eq get_uvm_def plus_prodE)
  then show ?thesis
    using EquiViper.add_masks_def by blast
qed

instance proof
  fix a b c ab bc :: "'a virtual_state"
  let ?a = "Rep_virtual_state a"
  let ?b = "Rep_virtual_state b"
  let ?c = "Rep_virtual_state c"
  let ?ab = "Rep_virtual_state ab"
  let ?bc = "Rep_virtual_state bc"

  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative plus_virtual_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (smt (verit, del_insts) EquiViper.compatible_virtual_state_implies_unbounded_virtual_state asso1 map_fun_apply plus_virtual_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
  proof (elim conjE)
    assume ab: "a \<oplus> b = Some ab" and bc: "b \<oplus> c = None"
    have ab_rep: "?a \<oplus> ?b = Some ?ab"
      using ab compatible_virtual_state_implies_unbounded_virtual_state by metis
    from bc consider (rep) "?b \<oplus> ?c = None" | (unbounded) "\<not> wf_mask_simple (the (get_vm b \<oplus> get_vm c))"
      by (auto simp add: virtual_state_plus_None)
    then show "ab \<oplus> c = None"
    proof cases
      case rep
      then show ?thesis
        using ab_rep asso2 virtual_state_plus_None by blast
    next
      case unbounded
      then obtain hl where "\<not> pwrite \<ge> the (get_vm b \<oplus> get_vm c) hl"
        by (meson wf_mask_simple_def)
      moreover have "the (get_vm b \<oplus> get_vm c) hl \<le> the (get_vm ab \<oplus> get_vm c) hl"
        unfolding plus_masks_the get_vm_plus[OF ab]
        by (metis add.assoc add.commute pos_perm_class.sum_larger)
      ultimately have "\<not> wf_mask_simple (the (get_vm ab \<oplus> get_vm c))"
        by (meson order.trans wf_mask_simple_def)
      then show ?thesis
        by (simp add: virtual_state_plus_None)
    qed
  qed

  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then show "Some a = a \<oplus> a"
    using compatible_virtual_state_implies_unbounded_virtual_state[of c c c]
      compatible_virtual_state_implies_unbounded_virtual_state[of c a b]
      compatible_virtual_state_implies_unbounded_virtual_state_rev[of a a a]
      positivity[of ?a ?b ?c]
    by fastforce
qed

end

lemma Rep_virtual_state_mono:
  assumes "\<phi>2 \<succeq> \<phi>1"
  shows "Rep_virtual_state \<phi>2 \<succeq> Rep_virtual_state \<phi>1"
proof -
  obtain \<phi>0 where "Some \<phi>2 = \<phi>1 \<oplus> \<phi>0"
    using assms greater_def by auto
  then have "Some (Rep_virtual_state \<phi>2) = Rep_virtual_state \<phi>1 \<oplus> Rep_virtual_state \<phi>0"
    by (rule compatible_virtual_state_implies_unbounded_virtual_state)
  then show ?thesis
    using greater_def by auto
qed

lemma get_vh_mono:
  assumes "\<phi>2 \<succeq> \<phi>1"
    and "get_vh \<phi>1 hl = Some v"
  shows "get_vh \<phi>2 hl = Some v"
  using assms(2) get_uvh_mono[OF Rep_virtual_state_mono[OF assms(1)]]
  by (simp add: get_vh.rep_eq)

subsection \<open>Normal equi_states\<close>

type_synonym 'a ag_trace = "(label \<rightharpoonup> 'a virtual_state) agreement"

type_synonym 'a equi_state = "('a val, ('a ag_trace \<times> 'a virtual_state)) abs_state"

definition get_state :: "'a equi_state \<Rightarrow> 'a virtual_state" where "get_state \<omega> = snd (snd \<omega>)"
definition get_trace :: "'a equi_state \<Rightarrow> (label \<rightharpoonup> 'a virtual_state)" where "get_trace \<omega> = the_ag (fst (snd \<omega>))"
definition set_state :: "'a equi_state \<Rightarrow> 'a virtual_state \<Rightarrow> 'a equi_state" where
  "set_state \<omega> \<phi> = (Ag (get_store \<omega>), (Ag (get_trace \<omega>), \<phi>))"
definition set_trace :: "'a equi_state \<Rightarrow> (label \<rightharpoonup> 'a virtual_state) \<Rightarrow> 'a equi_state" where
  "set_trace \<omega> \<tau> = (Ag (get_store \<omega>), (Ag \<tau>, get_state \<omega>))"

lemma get_store_set_trace [simp] :
  "get_store (set_trace \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_trace_def)
lemma get_store_set_state [simp] :
  "get_store (set_state \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_state_def)

lemma get_trace_set_store [simp] :
  "get_trace (set_store \<omega> st) = get_trace \<omega>"
  by (simp add: get_abs_state_def get_trace_def set_store_def)
lemma get_trace_set_trace [simp] :
  "get_trace (set_trace \<omega> t) = t"
  by (simp add:get_trace_def set_trace_def)
lemma get_trace_set_state [simp] :
  "get_trace (set_state \<omega> st) = get_trace \<omega>"
  by (simp add:get_trace_def set_state_def)

lemma get_state_set_store [simp] :
  "get_state (set_store \<omega> st) = get_state \<omega>"
  by (metis get_abs_state_def get_abs_state_set_store get_state_def)
lemma get_state_set_trace [simp] :
  "get_state (set_trace \<omega> st) = get_state \<omega>"
  by (simp add:get_state_def set_trace_def)
lemma get_state_set_state [simp] :
  "get_state (set_state \<omega> st) = st"
  by (simp add:get_state_def set_state_def)


lemma snd_get_abs_state :
  "snd (get_abs_state \<omega>) = get_state \<omega>"
  by (simp add: get_abs_state_def get_state_def)

lemma fst_get_abs_state :
  "the_ag (fst (get_abs_state \<omega>)) = get_trace \<omega>"
  by (simp add: get_abs_state_def get_trace_def)


abbreviation get_h where "get_h \<omega> \<equiv> get_vh (get_state \<omega>)"
abbreviation get_m where "get_m \<omega> \<equiv> get_vm (get_state \<omega>)"


fun get_pv :: "'a equi_state \<Rightarrow> 'a pre_virtual_state" where "get_pv \<omega> = vs2tuple (get_state \<omega>)"

definition shift_and_add_equi_state where
  "shift_and_add_equi_state \<omega> x = set_store \<omega> (shift_and_add (get_store \<omega>) x)"

subsection \<open>Assertions\<close>

inductive red_pure :: "('v, ('v virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state \<Rightarrow> 'v extended_val \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>] _)" [51,0,0,0] 81)
  and red_pure_exps :: "('v, ('v virtual_state)) interp \<Rightarrow> 'v equi_state \<Rightarrow> pure_exp list \<Rightarrow> 'v val list \<Rightarrow> bool"
  where
    RedPureExps: "\<lbrakk> list_all2 (\<lambda>e v. c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vals \<rbrakk> \<Longrightarrow> red_pure_exps c \<omega> exps vals"

\<comment>\<open>Independent of SA\<close>
| RedLit: "\<Delta> \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>] Val (val_of_lit l)"
| RedVar: "\<lbrakk> get_store \<omega> n = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>] Val v"

| RedUnop: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v ; eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>] Val v'"

| RedBinopLazy: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>
    \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] Val v"

| RedBinop: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v2 ; eval_binop v1 bop v2 = BinopNormal v \<rbrakk>
    \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] Val v"

| RedOld: "\<lbrakk> get_trace \<omega> l = Some \<phi> ; \<Delta> \<turnstile> \<langle>e; set_state \<omega> \<phi>\<rangle> [\<Down>] v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Old l e; \<omega>\<rangle> [\<Down>] v" (* Implicitly propagates failures *)

| RedLet: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; shift_and_add_equi_state \<omega> v1\<rangle> [\<Down>] r \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>] r"


| RedExistsTrue: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty ;
    \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool True) ;
    \<And>v'. v' \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v'\<rangle> [\<Down>] Val (VBool b) \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] Val (VBool True)"


| RedExistsFalse: "\<lbrakk> \<And>v. v \<in> set_from_type (domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool False) \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] Val (VBool False)"
| RedForallTrue: "\<lbrakk> \<And>v. v \<in> set_from_type (domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool True) \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] Val (VBool True)"
| RedForallFalse: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty ;
\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool False);
\<And>v'. v' \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v'\<rangle> [\<Down>] Val (VBool b) \<rbrakk>

\<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] Val (VBool False)"
| RedCondExpTrue: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VBool True) ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] r \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>] r"

| RedCondExpFalse: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VBool False) ; \<Delta> \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>] r \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>] r"
| RedPermNull: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef Null) \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"

| RedResult: "\<lbrakk> get_store \<omega> 0 = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>] Val v"



| RedBinopRightFailure: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] VFailure ;  eval_binop_lazy v1 bop = None \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] VFailure"
| RedBinopFailure: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v2 ; eval_binop v1 bop v2 = BinopOpFailure ; eval_binop_lazy v1 bop = None \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] VFailure" (* Division by 0 *)
| RedOldFailure: "\<lbrakk> get_trace \<omega> l = None \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Old l e ; \<omega>\<rangle> [\<Down>] VFailure"
| RedExistsFailure: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty; \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] VFailure \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] VFailure"
| RedForallFailure: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty; \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] VFailure \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] VFailure"
| RedPropagateFailure: "\<lbrakk> e \<in> sub_pure_exp e' ; \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow>  \<Delta> \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>] VFailure"



(* Dependent on the parameters *)
| RedField: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef (Address a)) ; read_field (Rep_virtual_state (get_state \<omega>)) (a, f) = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>] Val v"

| RedFunApp: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (funs \<Delta>) f vals (get_state \<omega>) = Some v \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>] Val v"
| RedFunAppFailure: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (funs \<Delta>) f vals (get_state \<omega>) = None \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>] VFailure"


(*
(*
| RedPermField: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef (Address a)) \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_preal (get_m \<omega> (a, f))))"
| RedPermPred: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_preal (get_m \<omega> (p, vals))))"
*)

(*
| RedUnfolding: "\<lbrakk> red_pure_exps \<Delta> (\<sigma>, \<tau>, \<phi>) exps vals ; unfold_pure \<phi> (P, vals) = Some \<phi>' ; \<Delta> \<turnstile> \<langle>e; (\<sigma>, \<tau>, \<phi>')\<rangle> [\<Down>] r \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>Unfolding P exps e; (\<sigma>, \<tau>, \<phi>)\<rangle> [\<Down>] r"
| RedUnfoldingFail: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; unfold_pure (get_state \<omega>) (P, vals) = None \<rbrakk>
\<Longrightarrow> \<Delta> \<turnstile> \<langle>Unfolding P exps e; \<omega>\<rangle> [\<Down>] VFailure"
*)
*)

inductive_cases red_pure_elim:
  "\<Delta> \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>] v"

inductive_simps red_pure_simps:
  "\<Delta> \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>] v"


text \<open>The following lemma proves that the meaning of pure expressions is independent from the interpretation of predicates.\<close>

lemma red_pure_indep_interp_pred:
  assumes "funs \<Delta> = funs \<Delta>'"
    and "domains \<Delta> = domains \<Delta>'"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v \<Longrightarrow> \<Delta>' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v"
    and "red_pure_exps \<Delta> \<omega> exps vals \<Longrightarrow> red_pure_exps \<Delta>' \<omega> exps vals"
  using assms
proof (induct rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c \<omega> exps vals)
  then show ?case
    by (simp add: list_all2_mono red_pure_red_pure_exps.RedPureExps)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLit)
next
  case (RedVar \<omega> n v \<Delta>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedVar)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedUnop)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopLazy)
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinop)
next
  case (RedOld \<omega> l \<phi> \<Delta> e v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedOld)
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLet)
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsTrue)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsFalse)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallTrue)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallFalse)
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPermNull)
next
  case (RedResult \<omega> v \<Delta>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedResult)
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopRightFailure)
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopFailure)
next
  case (RedOldFailure \<omega> l \<Delta> e)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedOldFailure)
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsFailure)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallFailure)
next
  case (RedPropagateFailure e e' \<Delta> \<omega>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPropagateFailure)
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedField)
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  then show ?case
    by (metis red_pure_red_pure_exps.RedFunApp)
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case
    by (metis red_pure_red_pure_exps.RedFunAppFailure)
qed


definition wd_pure :: "('v, ('v virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state \<Rightarrow> bool" where
  "wd_pure c e \<omega> \<longleftrightarrow> (\<exists>v. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v))"

definition wd_pure_set :: "('v, ('v virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state set \<Rightarrow> bool" where
  "wd_pure_set c e A \<longleftrightarrow> (\<forall>\<omega> \<in> A. wd_pure c e \<omega>)"

fun red_pure_bool where
  "red_pure_bool \<Delta> e \<omega> = (if wd_pure \<Delta> e \<omega> then
if \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool True) then Some True else Some False
else None)"

inductive red_atomic_assert :: "('v, ('v virtual_state)) interp \<Rightarrow> pure_exp atomic_assert \<Rightarrow> 'v equi_state \<Rightarrow> bool option \<Rightarrow> bool" where

RedAtomicPure: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VBool b)) \<rbrakk> \<Longrightarrow> red_atomic_assert \<Delta> (Pure e) \<omega> (Some b)"

\<comment>\<open>acc(e.f, p)\<close>
| RedAtomicAcc: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef r)) ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v > 0 \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> (Some (is_address r \<and> get_m \<omega> (the_address r, f) \<ge> Abs_preal v))"
| RedAtomicAccZero: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef _)) ; red_pure \<Delta> p \<omega> (Val (VPerm 0)) \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> (Some True)"

| RedAtomicAccWildcard: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef (Address a))) \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (Acc e f Wildcard) \<omega> (Some (get_m \<omega> (a, f) > 0))"
| RedAtomicAccWildcardNull: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef Null)) \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (Acc e f Wildcard) \<omega> (Some False)"
| RedAtomicAccNeg: "\<lbrakk> red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v < 0 \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> None"

\<comment>\<open>acc(P(exps), p)\<close>
(*
| RedAtomicPred: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v \<ge> 0 ; predicates \<Delta> (P, vals) = Some A \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> (Some (v > 0 \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = (Abs_preal v) \<odot> a)))"
| RedAtomicPredWildcard: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (predicates \<Delta>) (P, vals) = Some A \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps Wildcard) \<omega> (Some (\<exists>a \<in> A. \<exists>\<alpha>. \<alpha> > 0 \<and> get_state \<omega> = \<alpha> \<odot> a))"
| RedAtomicPredNeg: "\<lbrakk> red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v < 0 \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> None"
*)

(*
| RedAtomicPredNone: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v \<ge> 0 ;
footprint_predicate (get_state \<omega>) (P, vals) (rat_to_b v) = None \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> (Some (v = 0))"
| RedAtomicPredWildcardNone: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; footprint_predicate (get_state \<omega>) (P, vals) f = None \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps Wildcard) \<omega> (Some False)"
*)

(*
lemma no_old_indep_trace:
  assumes "no_old e"
  and       "fst x = fst x'" and
        "get_state x = get_state x'"
  shows "e x = Some v \<longleftrightarrow> e x' = Some v"

*)


fun sat :: "('a, 'a virtual_state) interp
\<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state \<Rightarrow> bool"

(* :: "'c \<Rightarrow> ('p, 'i) assert \<Rightarrow> 'a \<Rightarrow> bool" *) ("_ \<Turnstile> ((\<langle>_;_\<rangle>))" [52,0,0] 84) where
"\<Delta> \<Turnstile> \<langle>Atomic A; \<omega>\<rangle> \<longleftrightarrow> red_atomic_assert \<Delta> A \<omega> (Some True)"
| "sat \<Delta> (Imp b A) \<omega> \<longleftrightarrow>  (\<exists>v. (\<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v) \<and> (v = VBool True \<longrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle>)))"
| "(\<Delta> \<Turnstile> \<langle>CondAssert b A B; \<omega>\<rangle>) \<longleftrightarrow> (\<exists>v. (\<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v) \<and> (v = VBool True  \<longrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle>)) \<and>
(v = VBool False \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>))
)"
| "(\<Delta> \<Turnstile> \<langle>A && B; \<omega>\<rangle>) \<longleftrightarrow> (\<exists>a b. ((Some \<omega> = a \<oplus> b) \<and> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<and> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>)))"
| "(\<Delta> \<Turnstile> \<langle>A --* B; \<omega>\<rangle>) \<longleftrightarrow> (\<forall>b a. Some b = \<omega> \<oplus> a \<and> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>))"
| "\<Delta> \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle> \<longleftrightarrow> (\<forall>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)"
| "\<Delta> \<Turnstile> \<langle>Exists ty A; \<omega>\<rangle> \<longleftrightarrow> (\<exists>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)"
| "(\<Delta> \<Turnstile> \<langle>ImpureAnd A B; \<omega>\<rangle>) \<longleftrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> \<and> \<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>)"
| "(\<Delta> \<Turnstile> \<langle>ImpureOr A B; \<omega>\<rangle>) \<longleftrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> \<or> \<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>)"


(*
| "c \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle> \<longleftrightarrow> (\<forall>l. finite_sublist (set_from_type c ty) l \<and> length l \<ge> 1 \<longrightarrow>
(\<exists>part. multi_plus part \<omega> \<and> length l = length part \<and> list_all2 (\<lambda>v a. (c \<Turnstile> \<langle>A; shift_and_add_equi_state a v\<rangle>)) l part))"
*)


section \<open>Restrictions\<close>

fun all_predicate_have_bodies where
  "all_predicate_have_bodies Pr \<longleftrightarrow> (\<forall>P decl. program.predicates Pr P = Some decl \<longrightarrow> predicate_decl.body decl \<noteq> None)"

fun wf_assert where
  "wf_assert Pr (AccPredicate P arg p) \<longleftrightarrow> (program.predicates Pr P \<noteq> None)"


fun no_predicate where
  "no_predicate (A && B) \<longleftrightarrow> no_predicate A \<and> no_predicate B"
| "no_predicate (Atomic (AccPredicate _ _ _)) \<longleftrightarrow> False"

fun wf_assertion where
  "wf_assertion Pr (A && B) \<longleftrightarrow> wf_assertion Pr A \<and> wf_assertion Pr B"
| "wf_assertion Pr (A --* B) \<longleftrightarrow> wf_assertion Pr A \<and> wf_assertion Pr B \<and> no_predicate A"


lemma predicate_body_good_case:
  assumes "program.predicates Pr p = Some P"
    and "predicate_decl.body P = Some A"
  shows "predicate_body Pr p = A"
  using assms predicate_body_def
  by simp


















(* DUMP OF a part of LiftSepAlgebra *)

subsection \<open>Normal states\<close>


lemma full_state_ext:
  assumes "get_store a = get_store b"
    and "get_state a = get_state b"
    and "get_trace a = get_trace b"
  shows "a = b"
  by (metis agreement.exhaust_sel assms get_state_def get_store_def get_trace_def prod_eqI)

lemma abs_state_ext_iff :
  "\<omega>1 = \<omega>2 \<longleftrightarrow> get_store \<omega>1 = get_store \<omega>2 \<and> get_trace \<omega>1 = get_trace \<omega>2 \<and> get_state \<omega>1 = get_state \<omega>2"
  using full_state_ext by blast


definition make_equi_state :: "(var \<rightharpoonup> 'a val) \<Rightarrow> (label \<rightharpoonup> 'a virtual_state) \<Rightarrow> 'a virtual_state \<Rightarrow> 'a equi_state" where
  "make_equi_state s t st = set_store (set_trace (set_state undefined st) t) s"

lemma get_store_make_equi_state[simp] :
  "get_store (make_equi_state s t st) = s"
  by (simp add:make_equi_state_def)
lemma get_trace_make_equi_state[simp] :
  "get_trace (make_equi_state s t st) = t"
  by (simp add:make_equi_state_def)
lemma get_state_make_equi_state[simp] :
  "get_state (make_equi_state s t st) = st"
  by (simp add:make_equi_state_def)
lemma set_store_make_equi_state[simp] :
  "set_store (make_equi_state s t st) s' = make_equi_state s' t st"
  by (simp add: EquiViper.full_state_ext)
lemma set_trace_make_equi_state[simp] :
  "set_trace (make_equi_state s t st) t' = make_equi_state s t' st"
  by (simp add: EquiViper.full_state_ext)
lemma set_state_make_equi_state[simp] :
  "set_state (make_equi_state s t st) st' = make_equi_state s t st'"
  by (simp add: EquiViper.full_state_ext)









end
