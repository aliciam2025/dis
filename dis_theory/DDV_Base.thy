(*  Title:      DDV_Base.thy
    Author:     Alicia Marinache
    Date:       June 11, 2024
    Modified:   June 12, 2024
*)

section \<open>Domain Data View Base\<close>

text \<open>The DDV base theory is built on top of the DDV Boolean Algebra 
      theory and it describes the data operators and their properies.\<close>

theory DDV_Base
  imports 
    DDV_BA
    SetComprehension

begin

text \<open>The DDV base is a DDV Boolean algebra with finite and well formed sdatums and sdatas\<close>
locale ddv_base = ddv_ba + 
  assumes a_fin: "a \<in> A\<^sub>A \<Longrightarrow> finite a"
      and dt_fin: "\<And>dt. dt \<in> SD \<Longrightarrow> finite dt"
      and dt_one_k: "\<And>dt. dt \<in> SD \<Longrightarrow> \<llangle>s, v\<rrangle> \<in> dt \<Longrightarrow> \<not>(\<exists>v'. v'\<noteq>v \<and> \<llangle>s, v'\<rrangle> \<in> dt)"
      and dt_v_in_k: "\<And>dt. dt \<in> SD \<Longrightarrow> \<llangle>s, v\<rrangle> \<in> dt \<Longrightarrow> v \<in> s"
      and dt_not_empty: "\<And>a dt. a \<in> A\<^sub>A \<Longrightarrow> dt \<in> a \<Longrightarrow> dt \<noteq> {}"
begin

subsection \<open>Data Operators: Definitions\<close>
subsubsection \<open>Definition of reduce/extend data operators\<close>

text \<open>Definition 4.4\<close>
(* {def:reducesd} *)
(*definition reduce_sd :: "sdatum \<Rightarrow> sort \<Rightarrow> sdatum" ("_\<down>\<^sub>_" [150] 151) where*)
definition reduce_sd :: "sdatum \<Rightarrow> sort \<Rightarrow> sdatum" ("_\<down>\<^sub>_")  where
  "(dt\<down>\<^sub>k) = {sv| sv. sv \<in> dt \<and> sv \<noteq>\<^sub>S k}"

text \<open>Definition 4.6\<close>
(* {def:reduce} *)
definition reduce :: "sdata \<Rightarrow> sort \<Rightarrow> sdata" ("_\<Down>\<^sub>_") where
  "(a\<Down>\<^sub>k) = {dt\<down>\<^sub>k| dt. dt \<in> a}"

definition k_in_dt :: "sort \<Rightarrow> sdatum \<Rightarrow> bool" (infixl "\<^bold>\<in>" 120) where
  "k \<^bold>\<in> dt = (\<exists>v\<in> k. \<llangle>k, v\<rrangle> \<in> dt)"
definition k_nin_dt :: "sort \<Rightarrow> sdatum \<Rightarrow> bool" (infixl "\<^bold>\<notin>" 120) where
  "k \<^bold>\<notin> dt = (\<not>(k \<^bold>\<in> dt))"
definition k_in_a :: "sort \<Rightarrow> sdata \<Rightarrow> bool" (infixl "\<in>\<^sub>a" 101)
  where "k \<in>\<^sub>a a = (\<exists>dt \<in> a. k \<^bold>\<in> dt)"

text \<open>Definition 4.7\<close>
(* {def:extendsd} *)
definition extend_sd :: "sdatum \<Rightarrow> sort \<Rightarrow> sdata" ("_\<up>\<^sup>_") where
  "(dt\<up>\<^sup>k) = (if k \<^bold>\<notin> dt then {dt} else {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k})"

text \<open>Definition 4.8\<close>
(* {def:extend} *)
definition extend :: "sdata \<Rightarrow> sort \<Rightarrow> sdata" ("_\<Up>\<^sup>_") where
  "(a\<Up>\<^sup>k) = \<Union>{dt\<up>\<^sup>k| dt. dt \<in> a}"

subsubsection \<open>Definition of floored/raised data operators\<close>
text \<open>Definition 4.11\<close>
(* {{def:floored}} *)
definition floored :: "sdata \<Rightarrow> sort \<Rightarrow> sdata" ("\<lfloor>_\<rfloor>\<^sub>_")  where
  "(\<lfloor>a\<rfloor>\<^sub>k) = {dt. dt \<in> a \<and> k \<^bold>\<in> dt}"

text \<open>Definition 4.12\<close>
(* {def:raised} *)
definition raised :: "sdata \<Rightarrow> sort \<Rightarrow> sdata" ("\<lceil>_\<rceil>\<^sup>_")  where
  "(\<lceil>a\<rceil>\<^sup>k) = {dt. dt \<in> a \<and> k \<^bold>\<notin> dt}"

end (* locale ddv_base *)

subsection \<open>Data Operators: Properties\<close>

subsubsection \<open>Properties of data operators: helpers\<close>
context ddv_base
begin

lemma (in ddv_base) dt_in_SD: 
  shows "dt \<in> SD"
  using a_in_SD by auto 

lemma (in ddv_base) dt_in_extenda:
  assumes "dt \<in> a"
  shows "(dt\<up>\<^sup>k) \<subseteq> (a\<Up>\<^sup>k)"
    using extend_def assms
    by auto  

lemma (in ddv_base) kv_nin_reduce:
  assumes "dt \<in> SD" "k \<in> \<U>" "v \<in> k"
  shows "\<llangle>k, v\<rrangle> \<notin> (dt\<down>\<^sub>k)"
  using assms dt_in_SD dt_v_in_k by auto

lemma (in ddv_base) k_nin_reduce: 
  assumes "dt \<in> SD" "k \<in> \<U>"
  shows "k \<^bold>\<notin> (dt\<down>\<^sub>k)"
  using assms kv_nin_reduce k_nin_dt_def k_in_dt_def by auto

lemma (in ddv_base) kv_nin_dt: 
  assumes "a \<in> A\<^sub>A" "dt \<in> a" "k \<^bold>\<notin> dt" 
  shows "\<not>(\<exists>v. \<llangle>k, v\<rrangle> \<in> dt)"
  using assms dt_one_k k_nin_dt_def k_in_dt_def dt_v_in_k dt_in_SD by metis

lemma (in ddv_base) dt_has_kv: 
  assumes "a \<in> A\<^sub>A" "dt \<in> a" 
  shows "\<exists>k v. \<llangle>k, v\<rrangle> \<in> dt"
  using assms a_fin dt_not_empty
  using a_in_one0 one_closed by blast 

lemma (in ddv_base) dt_and_reduce:
  assumes "a \<in> A\<^sub>A" "dt \<in> a"  
  shows "dt = (dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}"
  using assms dt_has_kv
  using dt_in_SD local.one_def one_closed by auto 

end (* \<open>Properties of data operators: helpers\<close> *)

subsubsection \<open>Properties of extend data operator w.r.t zero and one\<close>
context ddv_base
begin

lemma (in ddv_base) zero_ext: "((\<^bold>0)\<Up>\<^sup>k) = \<^bold>0"
  using zero_def extend_def
  by simp

lemma (in ddv_base) one_ext: "((\<^bold>1)\<Up>\<^sup>k) = \<^bold>1"
  using one_def extend_def dt_in_SD dt_not_empty one_closed by fastforce

end (* \<open>Properties of extend data operator w.r.t zero and one\<close> *)

text \<open>Properties of data operators \<open>\<bowtie>\<close>, \<open>\<down>\<close>, \<open>\<up>\<close>, \<open>\<Down>\<close>, \<open>\<Up>\<close>\<close>
subsubsection \<open>Proposition 4.3.5\<close>
(* prop:reducesd_lambda_on_kappa *)
context ddv_base
begin
lemma (in ddv_base) reduce_sd_kappa_on_kappa: 
  assumes "k \<in> \<U>"
  shows "({\<llangle>k, v\<rrangle>}\<down>\<^sub>k) = {}"
proof -
  have "({\<llangle>k, v\<rrangle>}\<down>\<^sub>k) = {sv| sv. sv = \<llangle>k, v\<rrangle> \<and> sv\<noteq>\<^sub>Sk}"
    using reduce_sd_def assms by auto
  then have "({\<llangle>k, v\<rrangle>}\<down>\<^sub>k) = {sv| sv. False}"
    using a_in_one0 dt_not_empty one_closed by blast
  then show ?thesis by auto 
qed

lemma (in ddv_base) reduce_sd_lambda_on_kappa: 
  assumes "k \<in> \<U>" "l \<in> \<U>" "k \<noteq> l"
  shows "({\<llangle>k, v\<rrangle>}\<down>\<^sub>l) = {\<llangle>k, v\<rrangle>}"
  using dt_in_SD dt_not_empty local.one_def one_closed by auto
end (* \<open>Proposition 4.3.5\<close> *)

subsubsection \<open>Proposition 4.3.6\<close> (*prop:disjoint_reduced_extended*)
context ddv_base
begin
lemma (in ddv_base) disjoint_reduced_extended: 
  assumes "a \<in> A\<^sub>A" "k \<in>\<^sub>a a"
  shows   "(a\<Down>\<^sub>k) \<inter> (a\<Up>\<^sup>k) = {}"
proof -
  have f: "a \<in> Fin"
    using assms a_fin Fin_is_finite by auto
  then show ?thesis
  proof (induct a)
    case emptyI
    then show ?case
      using zero_def zero_ext by auto 
  next
    case (insertI a dt)
    then show ?case
      by (meson all_not_in_conv dt_in_SD dt_v_in_k insertI1) 
  qed
qed
end (* \<open>Proposition 4.3.6\<close> *)

subsubsection \<open>Proposition 4.3.7\<close> (*prop:reduce_extend_distr_union_int*)
context ddv_base
begin

text \<open>Proposition 4.3.7, Eq.1\<close>
lemma (in ddv_base) reducesd_distr_union: "((dt\<^sub>1 \<union> dt\<^sub>2)\<down>\<^sub>k) = (dt\<^sub>1\<down>\<^sub>k) \<union> (dt\<^sub>2\<down>\<^sub>k)"
  using reduce_sd_def setcomp_union by auto
(*
proof - 
  have f1: "((dt\<^sub>1 \<union> dt\<^sub>2)\<down>\<^sub>k) = {\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> (dt\<^sub>1 \<union> dt\<^sub>2) \<and> s\<noteq>k}"
    using reduce_sd_def by auto
  have f2: "{\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> (dt\<^sub>1 \<union> dt\<^sub>2) \<and> s\<noteq>k} = 
        {\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> dt\<^sub>1 \<and> s\<noteq>k} \<union>
        {\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> dt\<^sub>2 \<and> s\<noteq>k}"
    using setcomp_union by auto
  have f3: "{\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> dt\<^sub>1 \<and> s\<noteq>k} \<union>
        {\<llangle>s, v\<rrangle>| s v. \<llangle>s, v\<rrangle> \<in> dt\<^sub>2 \<and> s\<noteq>k} = (dt\<^sub>1\<down>\<^sub>k) \<union> (dt\<^sub>2\<down>\<^sub>k)" 
    using reduce_sd_def by auto
  then show ?thesis using f1 f2 f3 by auto 
qed
*)

text \<open>Proposition 4.3.7, Eq.2\<close>
lemma (in ddv_base) reducesd_distr_int: "((dt\<^sub>1 \<inter> dt\<^sub>2)\<down>\<^sub>k) = (dt\<^sub>1\<down>\<^sub>k) \<inter> (dt\<^sub>2\<down>\<^sub>k)"
proof - 
  have f1: "((dt\<^sub>1 \<inter> dt\<^sub>2)\<down>\<^sub>k) = {sv| sv. sv \<in> dt\<^sub>1 \<inter> dt\<^sub>2 \<and> sv \<noteq>\<^sub>S k}"
    using reduce_sd_def by auto
  have f2: "{sv| sv. sv \<in> dt\<^sub>1 \<inter> dt\<^sub>2 \<and> sv \<noteq>\<^sub>S k} = 
            {sv| sv. (sv \<in> dt\<^sub>1 \<and> sv \<noteq>\<^sub>S k) \<and> (sv \<in> dt\<^sub>2 \<and> sv \<noteq>\<^sub>S k)}"
    by auto
  have "{sv| sv. (sv \<in> dt\<^sub>1 \<and> sv \<noteq>\<^sub>S k) \<and> (sv \<in> dt\<^sub>2 \<and> sv \<noteq>\<^sub>S k)} = 
            {sv| sv. sv \<in> dt\<^sub>1 \<and> sv \<noteq>\<^sub>S k} \<inter> {sv| sv. sv \<in> dt\<^sub>2 \<and> sv \<noteq>\<^sub>S k}"
    by blast
  then show ?thesis 
    using f1 f2 reduce_sd_def by auto
qed

text \<open>Proposition 4.3.7, Eq.3\<close>
lemma (in ddv_base) reduce_distr_union: "((a \<union> b)\<Down>\<^sub>k) = (a\<Down>\<^sub>k) \<union> (b\<Down>\<^sub>k)"
  using reduce_def reduce_sd_def setcomp_union by auto

text \<open>Proposition 4.3.7, Eq.4\<close>
lemma (in ddv_base) reduce_distr_int: "((a \<inter> b)\<Down>\<^sub>k) \<subseteq> (a\<Down>\<^sub>k) \<inter> (b\<Down>\<^sub>k)"
proof -
  have f1: "((b \<union> (a \<inter> b))\<Down>\<^sub>k) = ((b\<Down>\<^sub>k) \<union> ((a \<inter> b)\<Down>\<^sub>k))"  (* b = b \<union> (a \<inter> b)*)
    by (metis reduce_distr_union)
  have "((a \<union> (a \<inter> b))\<Down>\<^sub>k) = ((a\<Down>\<^sub>k) \<union> ((a \<inter> b)\<Down>\<^sub>k))"
    by (metis reduce_distr_union)
  then show ?thesis
    using f1 by (simp add: sup.absorb_iff1 sup_inf_distrib2)
qed

text \<open>Proposition 4.3.7, Eq.5\<close>
lemma (in ddv_base) extend_distr_union: "((a \<union> b)\<Up>\<^sup>k) = (a\<Up>\<^sup>k) \<union> (b\<Up>\<^sup>k)"
  using extend_def setcomp_union by auto

text \<open>Proposition 4.3.7, Eq.6\<close>
lemma (in ddv_base) extend_distr_int0: "((a \<inter> b)\<Up>\<^sup>k) \<subseteq> (a\<Up>\<^sup>k) \<inter> (b\<Up>\<^sup>k)"
proof -
  have f1: "((b \<union> (a \<inter> b))\<Up>\<^sup>k) = ((b\<Up>\<^sup>k) \<union> ((a \<inter> b)\<Up>\<^sup>k))"  (* b = b \<union> (a \<inter> b)*)
    by (metis extend_distr_union)
  have "((a \<union> (a \<inter> b))\<Up>\<^sup>k) = ((a\<Up>\<^sup>k) \<union> ((a \<inter> b)\<Up>\<^sup>k))"
    by (metis extend_distr_union)
  then show ?thesis
    using f1 by (simp add: sup.absorb_iff1 sup_inf_distrib2)
qed
end (* \<open>Proposition 4.3.7\<close> *)

subsubsection \<open>Proposition 4.3.8\<close> (*prop:reduce_extend_idemp*)
context ddv_base
begin

text \<open>Proposition 4.4.6, Eq.1\<close>
lemma (in ddv_base) reducesd_idemp: "((dt\<down>\<^sub>k)\<down>\<^sub>k) = (dt\<down>\<^sub>k)"
proof - 
  have "((dt\<down>\<^sub>k)\<down>\<^sub>k) = {sv| sv. sv \<in> (dt\<down>\<^sub>k) \<and> sv \<noteq>\<^sub>S k}"
    using reduce_sd_def by auto 
  have "{sv| sv. sv \<in> (dt\<down>\<^sub>k) \<and> sv \<noteq>\<^sub>S k} = 
        {sv| sv. sv \<in> {sv'| sv'. sv' \<in> dt \<and> sv' \<noteq>\<^sub>S k} \<and> sv \<noteq>\<^sub>S k}"
    using reduce_sd_def by auto 
  have "{sv| sv. sv \<in> {sv'| sv'. sv' \<in> dt \<and> sv' \<noteq>\<^sub>S k} \<and> sv \<noteq>\<^sub>S k} = 
        {sv| sv. sv \<in> dt \<and> sv \<noteq>\<^sub>S k}"
    by blast
  then show ?thesis using reduce_sd_def by auto
qed

text \<open>Proposition 4.3.8, Eq.2\<close>
lemma (in ddv_base) extsd_idemp: "((dt\<up>\<^sup>k)\<Up>\<^sup>k) = (dt\<up>\<^sup>k)"
  using dt_in_SD dt_not_empty local.one_def one_closed by auto

(*
text \<open>Proposition 4.3.8, Eq.4\<close>
lemma (in ddv_base) extend_sd_idemp: 
  assumes "dt \<in> SD" "k \<in> \<U>"
  shows "((dt\<up>\<^sup>k)\<Up>\<^sup>k) = (dt\<up>\<^sup>k)"
proof - 
  have f0: "((dt\<up>\<^sup>k)\<Up>\<^sup>k) = \<Union>{(dt'\<up>\<^sup>k)| dt'. dt' \<in> (dt\<up>\<^sup>k)}" 
    using extend_def by auto
  consider (k_in_dt) "k \<^bold>\<in> dt" | (k_nin_dt) "k \<^bold>\<notin> dt"
    using k_nin_dt_def by auto
  then show ?thesis 
  proof cases
    case k_in_dt
    have f1: "{(dt'\<up>\<^sup>k)| dt'. dt' \<in> (dt\<up>\<^sup>k)} = 
              {(dt'\<up>\<^sup>k)| dt'. dt' \<in> {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k}}"
      using extend_sd_def k_in_dt k_nin_dt_def by auto
    have f2: "{(dt'\<up>\<^sup>k)| dt'. dt' \<in> {(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}| v. v \<in> k}} = 
              {((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<up>\<^sup>k| v. v \<in> k}" 
      by auto
    have f3: "{((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<up>\<^sup>k| v. v \<in> k} = 
              {{(((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>} | v'. v' \<in> k} | v. v \<in> k}"
      using extend_sd_def
      by (meson Set.set_insert dt_in_SD dt_v_in_k insertI1) 
    have f4: "v \<in> k \<Longrightarrow> (((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) = (dt\<down>\<^sub>k)"
      using assms reducesd_distr_union reducesd_idemp reduce_sd_kappa_on_kappa
      by blast
    have f5: "{{(((dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>})\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>} | v'. v' \<in> k} | v. v \<in> k} = 
              {{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k} | v. v \<in> k}"
      by (meson dt_in_SD dt_v_in_k empty_iff insertI1)
    have f6: "{{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v'\<rrangle>}| v'. v' \<in> k} | v. v \<in> k} = 
              {{(dt\<down>\<^sub>k) \<union> {\<llangle>k, v\<rrangle>}}| v. v \<in> k}"
      using dt_in_SD dt_v_in_k by blast
    then show ?thesis
      by (meson Set.set_insert a_in_SD dt_v_in_k insertI1 insert_subset)
  next
    case k_nin_dt
    have f1: "\<Union>{(dt'\<up>\<^sup>k)| dt'. dt' \<in> (dt\<up>\<^sup>k)} = \<Union>{(dt'\<up>\<^sup>k)| dt'. dt' \<in> {dt}}"
      using extend_sd_def k_nin_dt by auto
    have f2: "\<Union>{(dt'\<up>\<^sup>k)| dt'. dt' \<in> {dt}} = (dt\<up>\<^sup>k)"
      by auto
    then show ?thesis using f0 f1 by auto
  qed
qed

*)
text \<open>Proposition 4.3.8, Eq.3\<close>
lemma (in ddv_base) extend_idemp: "((a\<Up>\<^sup>k)\<Up>\<^sup>k) = (a\<Up>\<^sup>k)"
  using dt_in_SD dt_not_empty local.one_def one_closed by auto

text \<open>Proposition 4.3.8, Eq.4\<close>
lemma (in ddv_base) reduce_idemp: "((a\<Down>\<^sub>k)\<Down>\<^sub>k) = (a\<Down>\<^sub>k)"
proof - 
  have f1: "((a\<Down>\<^sub>k)\<Down>\<^sub>k) = {dt\<down>\<^sub>k| dt. dt \<in> (a\<Down>\<^sub>k)}"
    using reduce_def by auto
  have f2: "{dt\<down>\<^sub>k| dt. dt \<in> (a\<Down>\<^sub>k)} = 
        {dt\<down>\<^sub>k| dt. dt \<in> {dt'\<down>\<^sub>k| dt'. dt' \<in> a}}"
    using reduce_def by auto
  have f3: "{dt\<down>\<^sub>k| dt. dt \<in> {dt'\<down>\<^sub>k| dt'. dt' \<in> a}} = 
        {(dt\<down>\<^sub>k)\<down>\<^sub>k| dt. dt \<in> a}" by auto
  have f4: "{(dt\<down>\<^sub>k)\<down>\<^sub>k| dt. dt \<in> a} = {dt\<down>\<^sub>k| dt. dt \<in> a}"
    using reducesd_idemp by auto
  then show ?thesis using reduce_def f1 f2 f3 by auto
qed

end (* \<open>Proposition 4.3.8\<close> *)

subsubsection \<open>Proposition 4.3.9\<close> (*prop:reduce_extend_assoc*)
context ddv_base
begin

text \<open>Proposition 4.3.9, Eq.1 - helper\<close>
lemma (in ddv_base) reduce_sd_assoc0: "((dt\<down>\<^sub>k)\<down>\<^sub>l) = {sv| sv. sv \<in> dt \<and> sv\<noteq>\<^sub>Sk \<and> sv \<noteq>\<^sub>Sl}"
proof - 
  have f1: "((dt\<down>\<^sub>k)\<down>\<^sub>l) = {sv| sv. sv \<in> (dt\<down>\<^sub>k) \<and> sv \<noteq>\<^sub>S l}"
    using reduce_sd_def by auto 
  have f2: "{sv| sv. sv \<in> (dt\<down>\<^sub>k) \<and> sv \<noteq>\<^sub>S l} = 
        {sv| sv. sv \<in> {sv'| sv'. sv' \<in> dt \<and> sv'\<noteq>\<^sub>Sk} \<and> sv\<noteq>\<^sub>Sl}"
    using reduce_sd_def by auto 
  have f3: "{sv| sv. sv \<in> {sv'| sv'. sv' \<in> dt \<and> sv'\<noteq>\<^sub>Sk} \<and> sv\<noteq>\<^sub>Sl} = 
        {sv| sv. sv \<in> dt \<and> sv\<noteq>\<^sub>Sk \<and> sv \<noteq>\<^sub>Sl}"
    using setcomp_and by blast
  then show ?thesis using f1 f2  by auto
qed

text \<open>Proposition 4.3.9, Eq.1\<close>
lemma (in ddv_base) reducesd_assoc: "((dt\<down>\<^sub>k)\<down>\<^sub>l) = ((dt\<down>\<^sub>l)\<down>\<^sub>k)"
  using reduce_sd_assoc0 by auto 


text \<open>Proposition 4.3.9, Eq.2 - helper\<close>
lemma (in ddv_base) reduce_assoc0: "((a\<Down>\<^sub>k)\<Down>\<^sub>l) = {(dt\<down>\<^sub>k)\<down>\<^sub>l| dt. dt \<in> a}"
proof - 
  have f1: "((a\<Down>\<^sub>k)\<Down>\<^sub>l) = {dt\<down>\<^sub>l| dt. dt \<in> (a\<Down>\<^sub>k)}"
    using reduce_def by auto
  have f2: "{dt\<down>\<^sub>l| dt. dt \<in> (a\<Down>\<^sub>k)} = {dt\<down>\<^sub>l| dt. dt \<in> {dt'\<down>\<^sub>k| dt'. dt'\<in>a}}"
    using reduce_def by auto
  have f3: "{dt\<down>\<^sub>l| dt. dt \<in> {dt'\<down>\<^sub>k| dt'. dt'\<in>a}} = 
           {(dt\<down>\<^sub>k)\<down>\<^sub>l| dt. dt \<in> a}"
    by auto
  then show ?thesis using f1 f2 by auto
qed

text \<open>Proposition 4.3.9, Eq.2\<close>
lemma (in ddv_base) reduce_assoc: "((a\<Down>\<^sub>k)\<Down>\<^sub>l) = ((a\<Down>\<^sub>l)\<Down>\<^sub>k)"
  using reduce_def reducesd_assoc reduce_assoc0 by auto

text \<open>Proposition 4.3.9, Eq.3 - helper\<close>
lemma (in ddv_base) extend_assoc_sg: "(({dt}\<Up>\<^sup>k)\<Up>\<^sup>l) = (({dt}\<Up>\<^sup>l)\<Up>\<^sup>k)"
proof - 
  consider (kl_in_dt) "k \<^bold>\<in> dt \<and> l \<^bold>\<in> dt" |
           (kl_nin_dt) "k \<^bold>\<notin> dt \<and> l \<^bold>\<notin> dt" |
           (k_in_dt) "k \<^bold>\<in> dt \<and> l \<^bold>\<notin> dt" |
           (l_in_dt) "k \<^bold>\<notin> dt \<and> l \<^bold>\<in> dt"
    using k_nin_dt_def by auto
  then show ?thesis
  proof cases
    case kl_in_dt
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast 
  next
    case kl_nin_dt
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast 
  next
    case k_in_dt
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast 
  next
    case l_in_dt
    then show ?thesis
      using dt_in_SD dt_v_in_k by blast 
  qed
qed
    
text \<open>Proposition 4.3.9, Eq.3\<close>
lemma (in ddv_base) extend_assoc: 
  assumes "a \<in> A\<^sub>A"
  shows "((a\<Up>\<^sup>k)\<Up>\<^sup>l) = ((a\<Up>\<^sup>l)\<Up>\<^sup>k)"
proof - 
  have "a \<in> Fin"
    using assms a_in_SD a_fin Fin_is_finite by auto
  then show ?thesis 
  proof (induct a)
    case emptyI
    then show ?case
      using zero_def zero_ext by auto 
  next
    case (insertI a dt)
    show ?case
    proof (cases "k=l")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis
        using extend_assoc_sg extend_distr_union
        by (metis insertI.hyps(2) insert_is_Un) 
    qed
  qed
qed

end (* \<open>Proposition 4.3.9\<close> *)

subsubsection \<open>Proposition 4.3.10\<close> (*prop:floor_raise*)
context ddv_base
begin

text \<open>Proposition 4.3.10, Eq.1\<close>
lemma (in ddv_base) floor_raise_union: "(\<lfloor>a\<rfloor>\<^sub>k) \<union> (\<lceil>a\<rceil>\<^sup>k) = a"
proof - 
  have f1: "(\<lfloor>a\<rfloor>\<^sub>k) \<union> (\<lceil>a\<rceil>\<^sup>k) = {dt. dt \<in> a \<and> k \<^bold>\<in> dt } \<union>
                             {dt. dt \<in> a \<and> k \<^bold>\<notin> dt }"
    using floored_def raised_def by auto
  have f2: "{dt. dt \<in> a \<and> k \<^bold>\<in> dt } \<union>
            {dt. dt \<in> a \<and> k \<^bold>\<notin> dt } = 
            {dt. (dt \<in> a \<and> k \<^bold>\<in> dt) \<or> (dt \<in> a \<and> k \<^bold>\<notin> dt) }"
    by (simp add: Collect_disj_eq)
  have "{dt. (dt \<in> a \<and> k \<^bold>\<in> dt) \<or>   
             (dt \<in> a \<and> k \<^bold>\<notin> dt) } = 
        {dt. dt \<in> a}"
    using k_nin_dt_def by auto
  then show ?thesis using f1 f2 by auto
qed

text \<open>Proposition 4.3.10, Eq.2\<close>
lemma (in ddv_base) floor_raise_disjoint: "(\<lfloor>a\<rfloor>\<^sub>k) \<inter> (\<lceil>a\<rceil>\<^sup>k) = {}"
proof - 
  have f1: "(\<lfloor>a\<rfloor>\<^sub>k) \<inter> (\<lceil>a\<rceil>\<^sup>k) = {dt. dt \<in> a \<and> k \<^bold>\<in> dt } \<inter>
                         {dt. dt \<in> a \<and> k \<^bold>\<notin> dt }"
    using floored_def raised_def by auto
  also have f2: "{dt. dt \<in> a \<and> k \<^bold>\<in> dt } \<inter>
            {dt. dt \<in> a \<and> k \<^bold>\<notin> dt } = 
            {dt. (dt \<in> a \<and> k \<^bold>\<in> dt) \<and> (dt \<in> a \<and> k \<^bold>\<notin> dt) }"
    using Collect_conj_eq by auto
  finally have "{dt. (dt \<in> a \<and> k \<^bold>\<in> dt) \<and> (dt \<in> a \<and> k \<^bold>\<notin> dt) } = {}"
    using k_nin_dt_def by auto 
  thus ?thesis using f1 f2 by auto
qed

end (* \<open>Proposition 4.3.10\<close> *)

lemma (in ddv_base) absorb_extend: "((a \<inter> b)\<Up>\<^sup>k) \<subseteq> (a\<Up>\<^sup>k)"
proof -
  have "(a = (a \<union> (a \<inter> b)))"
    by blast
  then show ?thesis
    by (metis (no_types) extend_distr_union sup.absorb_iff1)
qed

end