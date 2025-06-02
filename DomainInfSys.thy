(*  Title:      DomainInfSys.thy
    Author:     Alicia Marinache
    Date:       August 1, 2023
    Modified:   June 13, 2024
*)

section \<open>Domain Information System\<close>

text \<open>In this section, the Domain Information System (DIS) is put together using 
      the DomainOnt and DomainDtVw components\<close>

theory DomainInfSys
  imports 
    DomainDtVw
    DomainOnt 
begin

locale dis = 
  ddv: domain_data_view where \<U> = \<U> and sort2name = sort2name and name2sort = name2sort and D = D + 
  dont: domain_ontology where A\<^sub>C = A\<^sub>C and A\<^sub>L = A\<^sub>L and \<G> = \<G>
 for   A\<^sub>C :: "'a concept set"
   and A\<^sub>L :: "'a concept set"
   and \<G> ::  "'a rgraph set"
   and \<U> :: "sort set" 
   and sort2name :: "sort \<Rightarrow> string"
   and name2sort :: "string \<Rightarrow> sort" 
   and D :: "sdatum set" +
 fixes sort2atom :: "sort \<Rightarrow> 'a" ("\<eta>_" [55]) 
 assumes sort2atom_inj: "\<eta> x = \<eta> y \<Longrightarrow> x = y"
begin

end

subsection \<open>Mapping Operator: Definitions\<close>
context dis
begin

definition (in dis) sval_sort :: "svalue \<Rightarrow> sort" ("\<tau>\<^sub>v_" [80]) where
  "\<tau>\<^sub>v sv \<equiv> name2sort (sname sv)"

text \<open>Definition 4.25\<close> (* {def:type} *)
definition (in dis) type :: "sdata \<Rightarrow> 'a concept" ("\<tau>_" [80]) where
  "\<tau> a = {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> a}}"
 (* "\<tau> a \<equiv> {\<eta> n | n. n \<in> \<tau>\<^sub>a a}"*)

definition (in dis) dtc_type :: "dataconcept \<Rightarrow> 'a concept" ("\<tau>\<^sub>d\<^sub>c_" [80]) where 
  "\<tau>\<^sub>d\<^sub>c c = \<Union>{\<tau> a| a. a \<in> c}"

text \<open>Syntactic sugar: notation for the top of the Boolean lattice\<close> 
definition (in dis) top_lattice :: "'a concept" 
  where "top_lattice = dont.clattice.topL"
notation top_lattice ("\<top>\<^sub>L")

end (* definitions *)

subsection \<open>Mapping Operator: Preserving Properties\<close>
context dis
begin

subsubsection \<open>Axiom 4.26\<close> (* {prop:type_preserve_plus} *)
text \<open>Axiom 4.26: Preserving the composition operator\<close>
lemma (in dis) type_plus: "\<tau> (a\<^bold>+b) = \<tau> a \<oplus>\<^sub>C \<tau> b"
proof -
  have "\<tau> (a\<^bold>+b) = {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> (a\<^bold>+b)}}"
    by (simp add: type_def)
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> (a\<^bold>+b)}} = 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> (a\<union>b)}}"
    by (simp add: ddv.plus_def)
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> (a\<union>b)}} = 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> a} \<union> \<Union>{dt. dt \<in> b}}"
    by auto
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> a} \<union> \<Union>{dt. dt \<in> b}} = 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> a}} \<union> 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> b}}"
    using set_image_union by (metis Union_Un_distrib)
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> a}} \<union> 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> b}} = (\<tau> a) \<union> (\<tau> b)"
    by (simp add: type_def)
  moreover have "(\<tau> a) \<union> (\<tau> b) = \<tau> a \<oplus>\<^sub>C \<tau> b"
    by (simp add: oplus_def)
  ultimately show ?thesis
    by auto
qed

subsubsection \<open>Axiom 4.27\<close> (* {prop:type_preserve_zero} *)
text \<open>Axiom 4.27: Preserving the zero\<close>
lemma (in dis) type_zero: "\<tau> \<^bold>0 = e\<^sub>C"
  by (simp add: type_def ddv.zero_def Concept.zero_def)
(*
proof - 
  have "\<tau> \<^bold>0 = {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> \<^bold>0}}"
    by (simp add: type_def)
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> \<^bold>0}} = 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> {}}}"
    by (simp add: ddv.zero_def)
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt. dt \<in> {}}} = 
                 {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> {}}"
    by auto
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> {}} = \<Union>{\<eta> (\<tau>\<^sub>v sv) | sv . False}"
    by simp
  moreover have "{\<eta> (\<tau>\<^sub>v sv) | sv . False} = {}"
    by simp
  ultimately show ?thesis
    by (simp add: Concept.zero_def)
qed
*)

subsubsection \<open>Axiom 4.28\<close> (* {prop:type_preserve_one} *)
text \<open>Axiom 4.28: Preserving the one\<close>
lemma (in dis) type_one: "\<tau> \<^bold>1 = \<top>\<^sub>L" 
proof - 
  have f1: "\<tau> \<^bold>1 = {\<eta> (\<tau>\<^sub>v sv) |sv. sv \<in> \<Union>{dt. dt \<in> \<^bold>1}}"
    by (simp add: type_def)
  have f2: "{\<eta> (\<tau>\<^sub>v sv) |sv. sv \<in> \<Union>{dt. dt \<in> \<^bold>1}} = 
            {\<eta> (\<tau>\<^sub>v sv) |sv. sv \<in> \<Union>{dt. dt \<in> \<bowtie>\<U>}}"
    by (simp add: ddv.one_def ddv.SD_def)
  then show ?thesis
    using dont.clattice.topL_def top_lattice_def ddv.one_def type_def
    by (meson Set.set_insert ddv.dt_in_SD ddv.dt_v_in_k insertI1) 
qed

end (* Mapping operator preserves operators *)

subsection \<open>Mapping Operator: Properties\<close>
subsubsection \<open>Properties of mapping operator: helpers\<close>
context dis
begin

lemma (in dis) type_mono: 
  assumes "a \<subseteq> b"
  shows "\<tau> a \<subseteq> \<tau> b"
proof - 
  have f1: "a \<union> b = b" 
    using assms by auto
  have f2: "\<tau> (a \<union> b) = \<tau> a \<union> \<tau> b"
    using type_plus ddv.plus_def oplus_def
    by metis
  then show ?thesis 
    using assms f1 by auto 
qed

lemma (in dis) k_in_a_in_type: 
  assumes "k \<in>\<^sub>a a" "a \<in> A\<^sub>A"
    shows "\<eta> k \<in> \<tau> a"
proof -
  have "a \<in> Fin"
    using assms ddv.a_in_SD ddv.a_fin Fin_is_finite by auto
  then show ?thesis
  proof - 
    obtain dt::sdatum where exDt: "dt \<in> a \<and> k \<^bold>\<in> dt"
      using assms ddv.k_in_a_def ddv.k_in_dt_def
      by auto 
    obtain v::dtype where exVDt: "\<llangle>k, v\<rrangle> \<in> dt"
      using exDt ddv.k_in_dt_def by auto
    obtain sv::svalue where exSv: "sv = \<llangle>k, v\<rrangle>"
      by auto
    have f1: "\<eta> k = \<eta> (\<tau>\<^sub>v sv)"
      using ddv.SD_def ddv.bow_zero_mono ddv.dt_not_empty ddv.one_closed ddv.one_def by auto
    have f2: "\<eta> (\<tau>\<^sub>v sv) \<in> {\<eta> (\<tau>\<^sub>v sv)| sv. sv \<in> \<Union>{dt| dt. dt \<in> a}}"
      using exDt exSv exVDt by blast
    then show ?thesis
      using f1 f2 type_def by auto
  qed
qed
end (* Mapping operator properties: helpers *)

subsubsection \<open>Proposition 4.6.1\<close>
context dis
begin

text \<open>Proposition 4.6.1 Equation 1\<close>
lemma (in dis) k_in_akextension: 
  assumes "a \<in> A\<^sub>A" "k \<in> \<U>" "\<exists>dt\<in>a. k \<^bold>\<in> dt" 
  shows "{(\<eta> k)} \<sqsubseteq>\<^sub>C \<tau> (a\<Up>\<^sup>k)"
proof -
    obtain dt::sdatum where exDt: "dt \<in> a \<and> k \<^bold>\<in> dt"
      using assms  ddv.k_in_dt_def
      by auto 
    obtain v::dtype where exVDt: "\<llangle>k, v\<rrangle> \<in> dt"
      using exDt ddv.k_in_dt_def by auto
    have f0: "dt \<in> a" 
      using exDt by auto 
  have f1: "(dt\<up>\<^sup>k) \<subseteq> (a\<Up>\<^sup>k)"
    using f0 ddv.dt_in_extenda by auto
  have f2: "\<tau> (dt\<up>\<^sup>k) = {\<eta> (\<tau>\<^sub>v sv) | sv . sv \<in> \<Union>{dt'. dt' \<in> (dt\<up>\<^sup>k)}}"
    using type_def by auto
  have f3: "\<llangle>k, v\<rrangle> \<in> \<Union>{dt'. dt' \<in> (dt\<up>\<^sup>k)}"
    using exVDt ddv.a_in_SD ddv.dt_not_empty ddv.one_closed ddv.one_def by blast 
  have f4: "(\<eta> k) = \<eta> (\<tau>\<^sub>v \<llangle>k, v\<rrangle>)"
    using assms ddv.dt_in_SD ddv.dt_v_in_k by blast
  have f5: "(\<eta> k) \<in> \<tau> (dt\<up>\<^sup>k)"
    using f2 f3 f4 by blast
  have f6: "\<tau> (dt\<up>\<^sup>k) \<subseteq> \<tau> (a\<Up>\<^sup>k)"
    using f1 type_def type_mono by auto
  then show ?thesis
    using f1 f5 f6 partOf_def by fastforce
qed

text \<open>Proposition 4.6.1 Equation 2\<close>
lemma (in dis) k_notin_kreduction: 
  assumes "k \<in> \<U>" "a \<in> A\<^sub>A"
  shows "(\<eta> k) \<notin> \<tau> (a\<Down>\<^sub>k)"
proof - 
  have f: "\<tau> (a\<Down>\<^sub>k) = {\<eta> (\<tau>\<^sub>v sv)| sv. sv \<in> \<Union>{dt\<down>\<^sub>k| dt. dt \<in> a}}"
    using type_def ddv.reduce_def by auto
  have "\<not>(\<exists>v. \<llangle>k, v\<rrangle> \<in> \<Union>{dt\<down>\<^sub>k| dt. dt \<in> a})"
    using assms ddv.kv_nin_reduce ddv.k_in_dt_def ddv.k_nin_dt_def
          ddv.dt_in_SD ddv.dt_not_empty ddv.one_closed ddv.one_def
    by metis
  then have "k \<notin> {(\<tau>\<^sub>v sv)| sv. sv \<in> \<Union>{dt\<down>\<^sub>k| dt. dt \<in> a}}"
    using sval_sort_def ddv.sort2name2sort ddv.sort_neq_def
          ddv.reduce_sd_def by force 
  then have "(\<eta> k) \<notin> {\<eta> (\<tau>\<^sub>v sv)| sv. sv \<in> \<Union>{dt\<down>\<^sub>k| dt. dt \<in> a}}"
    using assms sort2atom_inj by blast
  then show ?thesis 
    using f by auto
qed
end

subsubsection \<open>Proposition 4.6.2\<close>
context dis
begin

text \<open>Proposition 4.6.2 Equation 1\<close>
lemma (in dis) type_prod_zero: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A" "\<tau> a \<otimes>\<^sub>C \<tau> b =  e\<^sub>C"
  shows "\<tau> (a \<^bold>* b) = e\<^sub>C"
proof - 
  have "a \<^bold>* b = \<^bold>0" 
  proof (rule ccontr)
    assume ab_zero: "a \<^bold>* b \<noteq> \<^bold>0"
    obtain dt::sdatum where exDt: "dt = (SOME dt. dt \<in> a \<^bold>* b)"
      using ab_zero mult_def ddv.zero_def ddv.dt_not_empty by auto
    have f1: "dt \<noteq> {}"
      using exDt ddv.dt_not_empty ddv.star_closed ddv.a_in_SD ddv.carrier_set_def by auto
    obtain sv::svalue where exSv: "sv = (SOME sv. sv \<in> dt)"
      using f1 by auto 
    obtain k::sort where letK: "k = \<tau>\<^sub>v sv"
      using exSv by auto
    have f2: "k \<in>\<^sub>a a \<and> k \<in>\<^sub>a b"
      using assms exSv ddv.k_in_a_def ddv.k_in_dt_def ddv.dt_in_SD ddv.dt_not_empty
      by (metis ddv.one_closed ddv.one_def)
    have f3: "\<eta> k \<in> \<tau> a \<and> \<eta> k \<in> \<tau> b"
      using f2 k_in_a_in_type assms by auto
    have f4: "\<eta> k \<in> \<tau> a \<otimes>\<^sub>C \<tau> b"
      using f3 dont.clattice.otimes_def by fastforce
    have f5: "\<tau> a \<otimes>\<^sub>C \<tau> b \<noteq> e\<^sub>C"
      using f4 zero_def by auto
    with \<open>\<tau> a \<otimes>\<^sub>C \<tau> b = e\<^sub>C\<close>  show False by auto
  qed
  then show ?thesis
    by (simp add: assms type_zero)
qed

text \<open>Proposition 4.6.2 Equation 2\<close>
lemma (in dis) type_prod_weak: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A" 
    shows "\<tau> (a \<^bold>* b) \<sqsubseteq>\<^sub>C (\<tau> a \<otimes>\<^sub>C \<tau> b)"
  by (simp add: ddv.star_def dont.clattice.otimes_def partOf_def type_mono)


text \<open>Proposition 4.6.2 Equation 3\<close>
lemma (in dis) type_on_bow:
  assumes "a \<in> A\<^sub>A" "T \<subseteq> \<U>" "a = \<bowtie>T"
  shows "\<tau> a = {\<eta> s | s. s \<in> T}"
  using assms ddv.bow_zero_mono ddv.dt_not_empty by blast

text \<open>Proposition 4.6.2 Equation 4\<close>
lemma (in dis) type_preserve_prod: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A" "T\<^sub>a \<subseteq> \<U>" "T\<^sub>b \<subseteq> \<U>" "a = \<bowtie>T\<^sub>a" "b = \<bowtie>T\<^sub>b"
    shows " \<tau>(a \<^bold>* b) = \<tau> a \<otimes>\<^sub>C \<tau> b"
  using assms ddv.bow_zero_mono ddv.dt_not_empty by blast

end

end (* theory DomainInfSys *)