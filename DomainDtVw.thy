(*  Title:      DomainDtVw.thy
    Author:     Alicia Marinache
    Date:       October 11, 2023
    Modified:   June 11, 2024
*)

section \<open>Domain Data View\<close>

text \<open>The Domain Data View is extending the base with the original dataset \<open>D\<close>, that may 
      be used for reasoning. \<close>

theory DomainDtVw
  imports
    DFCylindricAlgebra
    DDV_Base
begin

type_synonym dataconcept = "sdata set"

locale domain_data_view = ddv_base + 
  fixes D :: "sdatum set"
begin

subsection \<open>Cylindrification Operator: Definition\<close>
definition cyl :: "sort \<Rightarrow> sdata \<Rightarrow> sdata" ("\<^bold>c\<^sub>_ _" 120) where
  "(\<^bold>c\<^sub>k a) \<equiv> \<Union>{dt\<up>\<^sup>k| dt. dt \<in> a}"

end (* locale domain_data_view *)

subsection \<open>Cylindrification Operator: Properties\<close>

subsubsection \<open>Axiom A.11\<close>
text \<open>Axiom A.11 of DIS: \<open>\<^bold>c\<^sub>k \<^bold>0 = \<^bold>0\<close>\<close>
context domain_data_view
begin
lemma (in domain_data_view)  cyl_zero: "(\<^bold>c\<^sub>k \<^bold>0) = \<^bold>0"
  using cyl_def zero_def zero_ext
  by simp
end

subsubsection \<open>Proposition 4.4.11\<close> (* {prop:cyl_plus} *)
text \<open>Cylindrification distributes over plus: \<open>\<forall>a b \<in> A\<^sub>A. \<^bold>c\<^sub>k (a \<^bold>+ b) = \<^bold>c\<^sub>k a \<^bold>+ \<^bold>c\<^sub>k b\<close>\<close>
context domain_data_view
begin
lemma (in domain_data_view) cyl_plus_sg: 
  assumes "a \<in> A\<^sub>A" and "dt \<in> SD" and "dt \<notin> a"
  shows "(\<^bold>c\<^sub>k ({dt} \<union> a)) = (\<^bold>c\<^sub>k {dt}) \<union> (\<^bold>c\<^sub>k a)"
proof - 
  have "a \<in> Fin"
    using assms a_in_SD a_fin Fin_is_finite by auto
  then show ?thesis
  proof (induct a)
    case emptyI
    then show ?case
      using cyl_zero zero_def by auto
  next
    case (insertI a dt')
    then show ?case 
      using dt_in_SD dt_v_in_k by blast 
  qed
qed

lemma (in domain_data_view) cyl_plus:
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A"
  shows "(\<^bold>c\<^sub>k (a \<^bold>+ b)) = (\<^bold>c\<^sub>k a) \<^bold>+ (\<^bold>c\<^sub>k b)"
proof - 
  have f: "a \<in> Fin"
    using \<open>a \<in> A\<^sub>A\<close> a_in_SD a_fin Fin_is_finite by auto
  then show ?thesis 
  proof (induct a arbitrary: b)
    case emptyI
    then show ?case 
      using cyl_zero zero_def plus_def by auto
  next
    case (insertI a dt)
    then show ?case
    proof (cases "dt \<notin> a")
      case True
      then show ?thesis
        by (meson Set.set_insert a_in_SD dt_v_in_k insert_subset subset_insertI) 
    next
      case False
      then show ?thesis
        by (simp add: insertI.hyps(2) insertI.prems insert_absorb)
    qed
  qed
qed
end

subsubsection \<open>Axiom A.12\<close>
text \<open>Axiom A.12 of DIS: \<open>\<forall>a \<in> A\<^sub>A. a < \<^bold>c\<^sub>k a\<close>\<close>
context domain_data_view
begin
lemma (in domain_data_view) cyl_le_sg:
  assumes "k \<in> \<U>" "a \<in> A\<^sub>A" "a = {dt}" 
  shows "a \<^bold>+ (\<^bold>c\<^sub>k a) = (\<^bold>c\<^sub>k a)"
proof - 
  have f: "(\<^bold>c\<^sub>k a) = (dt\<up>\<^sup>k)"
    using cyl_def assms by auto
  then show ?thesis
  proof (cases "k \<^bold>\<in> dt")
    case True
      have "(dt\<up>\<^sup>k) = {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k}"
        using extend_sd_def True k_nin_dt_def by auto 
      obtain v::dtype where v: "(\<llangle>k, v\<rrangle> \<in> dt)"
        using True k_in_dt_def by auto
      have "dt = (dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}"
        using assms dt_and_reduce v dt_in_SD dt_in_SD by blast
      have "{dt} \<union> (dt\<up>\<^sup>k) = (dt\<up>\<^sup>k)"
        using dt_in_SD dt_not_empty local.one_def one_closed by auto
      then show ?thesis
        using assms f plus_def by auto 
  next
    case False
    have "(\<^bold>c\<^sub>k a) = a"
    proof - 
      have "(dt\<up>\<^sup>k) = {dt}"
        using extend_sd_def False kv_nin_reduce k_nin_dt_def by auto
      then show ?thesis using assms f by auto
    qed
    then show ?thesis 
      using plus_def assms by auto
  qed
qed

lemma (in domain_data_view) cyl_le: 
  assumes "a \<in> A\<^sub>A" "k \<in> \<U>"
  shows "a \<^bold>+ (\<^bold>c\<^sub>k a) = (\<^bold>c\<^sub>k a)"
proof - 
  have "a \<in> Fin" 
    using assms a_fin a_in_SD Fin_is_finite by auto   
  then show ?thesis 
  proof (induct a)
    case emptyI
    then show ?case
      using plus_zero_l zero_def by auto 
  next
    case (insertI a dt)
    then show ?case
    proof (cases "dt \<in> a")
      case True
      then show ?thesis
        by (simp add: insertI.hyps(2) insert_absorb) 
    next
      case False
      have "(\<^bold>c\<^sub>k (a \<union> {dt})) = (\<^bold>c\<^sub>k a) \<union> (\<^bold>c\<^sub>k {dt})"
        using cyl_plus plus_def dt_in_SD
        by (metis Diff_iff dt_v_in_k insertI1)
      then have f: "(\<^bold>c\<^sub>k (insert dt a)) = (\<^bold>c\<^sub>k {dt}) \<union> (\<^bold>c\<^sub>k a)" 
        by (simp add: Un_commute) 
      have f3: "{dt} \<union> (\<^bold>c\<^sub>k {dt}) = (\<^bold>c\<^sub>k {dt})"
        using assms cyl_le_sg cyl_plus_sg assms
        using ddv_ba.dt_in_SD ddv_ba_axioms dt_in_SD plus_def by auto
      then show ?thesis
        using f insertI.hyps(2) plus_def by auto 
    qed
  qed
qed
end

subsubsection \<open>Proposition 4.4.12\<close> (* {{prop:cyl_idmp}} *)
text \<open>Idempotency of cylindrification operator: \<open>\<forall>a \<in> SD. \<forall>k \<in> \<U>. \<^bold>c\<^sub>k(\<^bold>c\<^sub>k a) = \<^bold>c\<^sub>k a\<close>\<close>
context domain_data_view
begin

lemma (in domain_data_view) cyl_assoc_sg: 
  assumes "dt \<in> SD"
  shows "(\<^bold>c\<^sub>k(\<^bold>c\<^sub>k {dt})) = (\<^bold>c\<^sub>k {dt})" 
proof - 
  have f: "(\<^bold>c\<^sub>k {dt}) = (dt\<up>\<^sup>k)"
    using cyl_def  by auto
  then show ?thesis
  proof (cases "k \<^bold>\<in> dt")
    case False
    have "(dt\<up>\<^sup>k) = {dt}"
      using extend_sd_def False kv_nin_reduce k_nin_dt_def by auto
    then show ?thesis using f by auto
  next
    case True
    (* k \<^bold>\<in> dt \<Longrightarrow> \<^bold>c\<^sub>k \<^bold>c\<^sub>k {dt} = \<^bold>c\<^sub>k {dt} *)
    have f1: "(\<^bold>c\<^sub>k (\<^bold>c\<^sub>k {dt})) = (\<^bold>c\<^sub>k (dt\<up>\<^sup>k))"
      using cyl_def by auto
    have f2: "(\<^bold>c\<^sub>k(dt\<up>\<^sup>k)) = \<Union>{x\<up>\<^sup>k| x. x \<in> (dt\<up>\<^sup>k)}"
      using cyl_def by auto
    have f3: "\<Union>{x\<up>\<^sup>k| x. x \<in> (dt\<up>\<^sup>k)} = \<Union>{x\<up>\<^sup>k| x. x \<in> {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k}}" 
      using extend_sd_def True k_nin_dt_def by auto
    have f4: "v \<in> k \<Longrightarrow> k \<^bold>\<in> ((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})"
      using k_in_dt_def by auto 
    have f5: "\<Union>{x\<up>\<^sup>k| x. x \<in> {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k}} = 
              \<Union>{((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<up>\<^sup>k | v. v \<in> k}"
      by auto
    have f6: "{((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<up>\<^sup>k | v. v \<in> k} = 
              {{(((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k }| v. v \<in> k}"
      using extend_sd_def f4 k_in_dt_def k_nin_dt_def extend_def
      by (meson Set.set_insert dt_in_SD dt_v_in_k insertI1)
    have f7: "(((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) = (dt\<down>\<^sub>k)"
      using kv_nin_reduce reducesd_distr_union reducesd_idemp 
            reduce_sd_lambda_on_kappa assms 
            dt_and_reduce local.one_def one_closed by presburger
    have f8: "{{(((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k }| v. v \<in> k} = 
              {{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k }}"
      by (meson Set.set_insert dt_in_SD dt_v_in_k insertI1)
    have "{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k } = (dt\<up>\<^sup>k)"
      using extend_sd_def True k_nin_dt_def by auto 
    then have "\<Union>{{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k }} = (\<^bold>c\<^sub>k {dt})"
      using cyl_def by auto
    then show ?thesis 
      using f1 f2 f3 f5 f6 f8 by presburger 
  qed
qed

lemma (in domain_data_view) cyl_assoc:
  assumes "a \<in> A\<^sub>A" "k \<in> \<U>"
  shows  "(\<^bold>c\<^sub>k(\<^bold>c\<^sub>k a)) = (\<^bold>c\<^sub>k a)"
proof - 
  have f: "a \<in> Fin"
    using assms a_fin a_in_SD Fin_is_finite by auto   
  then show ?thesis
  proof (induct a)
    case emptyI
    then show ?case using cyl_zero zero_def by auto
  next
    case (insertI a dt)
    then show ?case
    proof (cases "dt \<in> a")
      case True
      then show ?thesis
        by (simp add: insertI.hyps(2) insert_absorb)
    next
      case False
      have "(\<^bold>c\<^sub>k (a \<union> {dt})) = (\<^bold>c\<^sub>k a) \<union> (\<^bold>c\<^sub>k {dt})"
        using cyl_plus plus_def dt_in_SD
        by (metis PowI a_in_SD carrier_set_def)
      then have f2: "(\<^bold>c\<^sub>k (insert dt a)) = (\<^bold>c\<^sub>k {dt}) \<union> (\<^bold>c\<^sub>k a)" 
        by auto
      have f3: "(\<^bold>c\<^sub>k(\<^bold>c\<^sub>k (insert dt a))) = (\<^bold>c\<^sub>k((\<^bold>c\<^sub>k {dt}) \<union> (\<^bold>c\<^sub>k a)))"
        using f2 cyl_plus plus_def
        by simp 
      have f4: "(\<^bold>c\<^sub>k((\<^bold>c\<^sub>k {dt}) \<union> (\<^bold>c\<^sub>k a))) = (\<^bold>c\<^sub>k(\<^bold>c\<^sub>k {dt})) \<union> (\<^bold>c\<^sub>k(\<^bold>c\<^sub>k a))"
        using cyl_plus plus_def
        by (meson Set.set_insert a_in_SD dt_v_in_k insertI1 insert_subset)
      then show ?thesis
        by (simp add: dt_in_SD cyl_assoc_sg f2 f4 insertI.hyps(2)) 
    qed
  qed
qed
end

subsubsection \<open>Axiom A.13\<close>
text \<open>Axiom A.13 of DIS: \<open>\<forall>a b \<in> A\<^sub>A. \<forall>k \<in> \<U>. \<^bold>c\<^sub>k (a \<^bold>* \<^bold>c\<^sub>k b) = \<^bold>c\<^sub>k a \<^bold>* \<^bold>c\<^sub>k b\<close>\<close>
context domain_data_view
begin
(*
lemma (in domain_data_view) cyl_mod_sg:
  assumes "dt\<^sub>1 \<in> SD" "dt\<^sub>2 \<in> SD" "k \<in> \<U>"
  shows  "(\<^bold>c\<^sub>k ({dt\<^sub>1} \<^bold>* (\<^bold>c\<^sub>k {dt\<^sub>2}))) = (\<^bold>c\<^sub>k {dt\<^sub>1}) \<^bold>* (\<^bold>c\<^sub>k {dt\<^sub>2})"
proof - 
  consider (k_in_both) "k \<^bold>\<in> dt\<^sub>1 \<and> k \<^bold>\<in> dt\<^sub>2" | 
           (k_in_none) "k \<^bold>\<notin> dt\<^sub>1 \<and> k \<^bold>\<notin> dt\<^sub>2" | 
           (k_in_dt1)  "k \<^bold>\<in> dt\<^sub>1 \<and> k \<^bold>\<notin> dt\<^sub>2" |
           (k_in_dt2)  "k \<^bold>\<notin> dt\<^sub>1 \<and> k \<^bold>\<in> dt\<^sub>2"
    using k_nin_dt_def by auto
  then show ?thesis 
  proof cases
    case k_in_both
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast
  next
    case k_in_none
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast
  next
    case k_in_dt1
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast
  next
    case k_in_dt2
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast
  qed
qed

lemma (in domain_data_view) cyl_mod_sg1: 
  assumes "a \<in> A\<^sub>A"
  shows "(\<^bold>c\<^sub>k ({dt} \<^bold>* (\<^bold>c\<^sub>k a))) = (\<^bold>c\<^sub>k {dt}) \<^bold>* (\<^bold>c\<^sub>k a)"
proof - 
  have f: "a \<in> Fin"
    using assms a_fin a_in_SD Fin_is_finite by auto   
  then show ?thesis
  proof (induct a)
    case emptyI
    then show ?case
      using cyl_zero star_zero_r zero_def by auto 
  next
    case (insertI a dt')
    then show ?case
      by (meson Set.set_insert a_in_SD dt_v_in_k insertI1 insert_subset)
  qed
qed
*)
lemma (in domain_data_view)  cyl_mod:
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A"
  shows "(\<^bold>c\<^sub>k (a \<^bold>* (\<^bold>c\<^sub>k b))) = (\<^bold>c\<^sub>k a) \<^bold>* (\<^bold>c\<^sub>k b)"
proof - 
  have f: "a \<in> Fin"
    using assms a_fin a_in_SD Fin_is_finite by auto   
  then show ?thesis
  proof (induct a arbitrary: b)
    case emptyI
    then show ?case
      using cyl_zero star_def zero_def by auto
  next
    case (insertI a dt)
    then show ?case 
      by (meson Set.set_insert a_in_SD dt_v_in_k insert_subset subset_insertI) 
  qed
qed
end

subsubsection \<open>Axiom A.13\<close>
text \<open>Axiom A.14 of DIS: \<open>\<forall>a \<in> A\<^sub>A. \<forall>k l \<in> \<U>. \<^bold>c\<^sub>k (\<^bold>c\<^sub>l a) = \<^bold>c\<^sub>l (\<^bold>c\<^sub>k a)\<close>\<close>
context domain_data_view
begin
lemma (in domain_data_view)  cyl_comm:
  assumes "a \<in> A\<^sub>A" 
  shows "(\<^bold>c\<^sub>k (\<^bold>c\<^sub>l a)) = (\<^bold>c\<^sub>l (\<^bold>c\<^sub>k a))"
proof - 
  have f: "a \<in> Fin" 
    using assms a_fin a_in_SD Fin_is_finite by auto   
  then show ?thesis
  proof (induct a)
    case emptyI
    then show ?case
      using cyl_zero zero_def by auto 
  next
    case (insertI a dt)
    then show ?case
      using dt_in_SD dt_not_empty local.one_def one_closed by auto 
  qed
qed
end

subsection \<open>Domain Data View: Properties\<close>
subsubsection \<open>DDV as model for a diagonal-free cylindric algebra\<close>
context domain_data_view
begin
interpretation dfcyl_algebra "(\<^bold>*)" "(\<^bold>+)" "(\<^bold>-)" "\<^bold>0" "\<^bold>1" "cyl" "A\<^sub>A"
 apply unfold_locales
  (* a \<^bold>* b \<^bold>* c = a \<^bold>* (b \<^bold>* c) *)
  apply (simp add: star_assoc)
  (* a \<^bold>* b = b \<^bold>* a *)
  apply (simp add: star_comm)
  (* a \<^bold>+ b \<^bold>+ c = a \<^bold>+ (b \<^bold>+ c) *)
  apply (simp add: plus_assoc)
  (* a \<^bold>+ b = b \<^bold>+ a *)
  apply (simp add: plus_comm)
  (* x \<^bold>* y \<^bold>+ z = (x \<^bold>* y) \<^bold>+ (x \<^bold>* z) *)
  apply (simp add: plus_distr_star)
  (* x \<^bold>+ (y \<^bold>* z) = x \<^bold>+ y \<^bold>* x \<^bold>+ z *)
  apply (simp add: star_distr_plus)
  (* x \<^bold>* \<^bold>1 = x *)
  apply (simp add: a_in_one0 star_def subset_antisym)
  (* x \<^bold>+ \<^bold>0 = x *)
  apply (simp add: plus_zero_r)
  (*  x \<^bold>* \<^bold>- x = \<^bold>0 *)
  apply (simp add: complement_star)
  (* x \<^bold>+ \<^bold>- x = \<^bold>1 *)
  apply (simp add: complement_plus0)
  (* \<^bold>c\<^sub>k \<^bold>0 = \<^bold>0 *)
  apply (simp add: cyl_zero)
  (* \<^bold>c\<^sub>k (x \<^bold>* \<^bold>c\<^sub>k y) = \<^bold>c\<^sub>k x \<^bold>* \<^bold>c\<^sub>k y *)
  apply (simp add: cyl_mod)
  (* \<^bold>c\<^sub>k (\<^bold>c\<^sub>l x) = \<^bold>c\<^sub>l (\<^bold>c\<^sub>k x) *)
  apply (simp add: cyl_comm)
  done
end (* DDV model for a df-cylindric algebra *)

context domain_data_view
begin
end

end (* theory DomainDtVw *)

