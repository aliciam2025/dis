(*  Title:      DDVUniverse.thy
    Author:     Alicia Marinache
    Date:       June 15, 2023
    Modified:   June 11, 2024
*)

section \<open>Domain Data View Universe\<close>

text \<open>The foundational element of the Domain Data View is a finite set of sorts, 
      called the universe. The sorts are given by the attributes of the dataset and 
      each sort consists of a finite set of values.\<close>

theory DDVUniverse
  imports DDVTypes 
          FinIndSet 
          "HOL-Library.FuncSet"
begin

locale universe =  
  fixes \<U> :: "sort set"
    and sort2name :: "sort \<Rightarrow> string"
    and name2sort :: "string \<Rightarrow> sort"

assumes U_notempty: "\<U> \<noteq> {}"
      and U_fin: "finite \<U>"
      and U_sorts_fin: "s \<in> \<U> \<Longrightarrow> finite s"
      and U_sorts_notempty: "s \<in> \<U> \<Longrightarrow> s \<noteq> {}"
      and sort2name_inj: "\<And>x y. x \<in> \<U> \<Longrightarrow> y \<in> \<U> \<Longrightarrow> sort2name x = sort2name y \<Longrightarrow> x = y"
      and sort2name_fun: "\<And>x y. x \<in> \<U> \<Longrightarrow> y \<in> \<U> \<Longrightarrow> x \<noteq> y \<Longrightarrow> sort2name x \<noteq> sort2name y"
      and sort2name2sort: "sort2name (name2sort n) = n"
      and name2sort2name: "\<And>s. s \<in> \<U> \<Longrightarrow> name2sort (sort2name s) = s" 
begin

text \<open>Syntactic sugar for \<^term>\<open>svalue\<close> construction\<close>
definition svalue_constr :: "sort \<Rightarrow> dtype \<Rightarrow> svalue" ("\<llangle>_, _\<rrangle>") where
  "\<llangle>s, v\<rrangle> = \<langle>sort2name s, v\<rangle>"

definition sort_eq :: "svalue \<Rightarrow> sort \<Rightarrow> bool" (infix "=\<^sub>S" 55) where 
  "sv =\<^sub>S k \<equiv> sname sv = sort2name k"
definition sort_neq :: "svalue \<Rightarrow> sort \<Rightarrow> bool" (infix "\<noteq>\<^sub>S" 55) where 
  "sv \<noteq>\<^sub>S k \<equiv> sname sv \<noteq> sort2name k"

lemma sort_svalue: "sname \<llangle>s, v\<rrangle> = sort2name s"
  by (simp add: make_svalue_def svalue_constr_def sname_def)

subsection \<open>Universe operators: Definitions\<close>
text \<open>Extension operator \<open>ext\<close> is used to construct \<open>SV\<close>, 
      the set of all possible svalues in the Universe.\<close>
definition ext :: "sort \<Rightarrow> svalue set" where
  "ext s = {\<llangle>s, v\<rrangle> | v. v \<in> s}"

definition SV :: "svalue set" where
  "SV = \<Union>{ext s | s. s \<in> \<U>}"

text \<open>\<open>SD\<close>, the set of all possible sdatas in the Universe, is defined using 
      the \<open>\<bowtie>\<close> operator, which in turn is defined through a special Carthesian product
      operator, \<open>pcart\<close>.\<close>
definition pcart :: "svalue set set \<Rightarrow> svalue set set"  where
  "pcart A = {X. \<exists>f. f \<in> X \<rightarrow> A \<and> inj_on f X \<and> (\<forall>x\<in>X. x \<in> f x)}"

definition bow :: "sort set \<Rightarrow> svalue set set" ("\<bowtie>") where 
  "\<bowtie>U = pcart (ext ` U)"

definition SD :: "sdatum set" where
  "SD = \<bowtie>\<U>"

end (* locale universe*)

subsection \<open>Universe operators: Properties\<close>
subsubsection \<open>Properties of Carthesian product operator\<close>
context universe
begin
lemma (in universe) pcartI:
  assumes "f \<in> X \<rightarrow> A" "inj_on f X" "\<And>x. x \<in> X \<Longrightarrow> x \<in> f x"
  shows   "X \<in> pcart A"
  using assms by (auto simp: pcart_def)

lemma (in universe) pcartE:
  assumes "X \<in> pcart A"
  obtains f where "f \<in> X \<rightarrow> A" "inj_on f X" "\<And>x. x \<in> X \<Longrightarrow> x \<in> f x"
  using assms by (auto simp: pcart_def)

lemma (in universe) pcart_mono:
  assumes "A \<subseteq> B"
  shows   "pcart A \<subseteq> pcart B"
  using assms unfolding pcart_def by fast

lemma (in universe) pcart_zero: "pcart {} = {{}}"
  using pcart_def by blast

lemma (in universe) pcart_insert:
  assumes "a \<notin> A"
  shows "pcart (insert a A) = pcart A \<union> {insert x y |x y. x \<in> a \<and> y \<in> pcart A}"
proof (intro equalityI subsetI)
  fix X assume "X \<in> pcart (insert a A)"
  then obtain f where f: "f \<in> X \<rightarrow> insert a A" "inj_on f X" "\<And>x. x \<in> X \<Longrightarrow> x \<in> f x"
    using pcartE by blast
  show "X \<in> pcart A \<union> {insert x y |x y. x \<in> a \<and> y \<in> pcart A}"
  proof (cases "a \<in> f ` X")
    case False
    have "X \<in> pcart A"
    proof (rule pcartI)
      show "f \<in> X \<rightarrow> A"
        using f False by (auto simp: Pi_def)
    qed (use f in auto)
    thus ?thesis
      by blast
  next
    case True
    obtain xa where xa: "xa \<in> X" "a = f xa"
      using True by blast
    have fa: "f \<in> X-{xa} \<rightarrow> A" "inj_on f X" "\<And>x. x \<in> X-{xa} \<Longrightarrow> x \<in> f x"
    proof -
      show "\<And>x. x \<in> X-{xa} \<Longrightarrow> x \<in> f x"
        using xa f(3) by auto
      show "inj_on f X" 
        using f(2) by auto
      then have f01:  "\<And>x. x \<in> X-{xa} \<Longrightarrow> f x \<noteq> a"
        using f(2) xa by (auto simp: inj_on_contraD) 
      then have f02:  "\<And>x. x \<in> X \<Longrightarrow> f x \<in> insert a A"
        using f(1) by auto
      then have "\<And>x. x \<in> X-{xa} \<Longrightarrow> f x \<in> A"
        using f01 f02 by auto
      then show "f \<in> X-{xa} \<rightarrow> A"
        using xa f(1) by auto 
    qed
    have X_xa: "X - {xa} \<in> pcart A"
      using pcartI xa fa by (meson inj_on_diff)
    have "{xa} \<in> {insert x y |x y. x \<in> a \<and> y \<in> pcart A}"
      using f pcart_def xa
    proof -
      have "{} \<in> {P. \<exists>f. f \<in> P \<rightarrow> A \<and> inj_on f P \<and> (\<forall>p. p \<in> P \<longrightarrow> p \<in> f p)}"
        by simp
      then have "\<exists>p P. {xa} = insert p P \<and> p \<in> a \<and> P \<in> pcart A"
        by (metis (lifting) f(3) pcart_def xa(1) xa(2))
      then show ?thesis
        by fastforce
    qed
    then show ?thesis
      using X_xa
      by (smt (verit, del_insts) UnI2 f insert_Diff mem_Collect_eq xa)
  qed
next
  fix X assume "X \<in> pcart A \<union> {insert x y |x y. x \<in> a \<and> y \<in> pcart A}"
  thus "X \<in> pcart (insert a A)"
  proof 
    assume "X \<in> pcart A"
    thus "X \<in> pcart (insert a A)"
      using pcart_mono by blast
  next
    assume "X \<in> {insert x y |x y. x \<in> a \<and> y \<in> pcart A}"
    then obtain x X' where *: "X = insert x X'" "x \<in> a" "X' \<in> pcart A"
      by blast                   
    then obtain f' where f': "f' \<in> X' \<rightarrow> A" "inj_on f' X'" "\<And>x'. x' \<in> X'\<Longrightarrow> x' \<in> f' x'"
      using pcartE by blast
    show "X \<in> pcart (insert a A)"
    proof (cases "x \<in> X'")
      case True
      then show ?thesis using f' *
        by (metis insert_absorb pcart_mono subsetD subset_insertI) 
    next
      case False
      obtain f where f: "f \<equiv> (\<lambda>w. if w = x then a else f' w)" 
        by auto 
      show ?thesis
      proof (rule pcartI)
        show "f \<in> X \<rightarrow> insert a A" 
          using f f' assms * Pi_I Pi_mem
          by (smt (verit) insert_iff) 
        show "inj_on f X"
           using f f' assms *
           by (smt (verit) Pi_iff inj_on_def insert_iff) 
         show "\<And>x. x \<in> X \<Longrightarrow> x \<in> f x"
           using f f' assms *
           by (metis insertE) 
       qed
    qed
  qed
qed
end

subsubsection \<open>Properties of sort extension operator\<close>
context universe
begin

lemma (in universe) extI:
  assumes "v \<in> s"
  shows   "\<llangle>s, v\<rrangle> \<in> ext s"
  using assms by (auto simp: ext_def)

lemma (in universe) extE:
  assumes "\<llangle>s, v\<rrangle> \<in> ext s"
  obtains v where "v \<in> s"
  using assms by (auto simp: ext_def)

lemma (in universe) ext_zero: 
  "ext {} = {}"
  using ext_def by auto

lemma (in universe) ext_nzero: 
  assumes "s \<noteq> {}"
  shows "ext s \<noteq> {}"
proof - 
  obtain v where v: "v = (SOME x. x \<in> s)" 
    using assms by auto
  then have "\<llangle>s, v\<rrangle> \<in> ext s"
    using v ext_def assms some_in_eq by auto 
  thus ?thesis  by auto 
qed

lemma (in universe) svconstr_neq_v:
  assumes "v1 \<noteq> v2 "
  shows "\<llangle>s, v1\<rrangle> \<noteq> \<llangle>s, v2\<rrangle>"
  using svalue_constr_def make_svalue_def assms svalue_neq_snd
  by (metis old.prod.inject) 

lemma (in universe) ext_v_nin_s: 
  assumes "v \<notin> s"
  shows "\<llangle>s, v\<rrangle> \<notin> ext s"
  by (smt (verit, ccfv_threshold) assms ext_def mem_Collect_eq svconstr_neq_v)

lemma (in universe) ext_neq_s: 
  assumes "s1 \<in> \<U>" "s2 \<in> \<U>" "s1 \<noteq> s2"
  shows "ext s1 \<noteq> ext s2"
proof (cases "s1\<noteq>{} \<and> s2\<noteq>{}")
  case False
  then show ?thesis using ext_zero ext_nzero False
    by (metis assms(3))
next
  case True
  obtain v1 where v1: "v1 = (SOME x. x \<in> s1)" using True by auto
  obtain v2 where v2: "v2 = (SOME x. x \<in> s2)" using True by auto
  have ev1: "\<llangle>s1, v1\<rrangle> \<in> ext s1"
    by (simp add: True extI some_in_eq v1)
  have ev2: "\<llangle>s2, v2\<rrangle> \<in> ext s2"
    by (simp add: True extI some_in_eq v2)
  have "\<llangle>s1, v1\<rrangle> \<noteq> \<llangle>s2, v2\<rrangle>" 
    using assms sort2name_fun svalue_neq_fst
    by (metis sort_svalue)
  then show ?thesis
    using True ev1 ev2
    by (smt (verit) assms ext_def mem_Collect_eq name2sort2name sort_svalue)
qed

lemma (in universe) ext_eq: 
  assumes "s1 \<in> \<U>" "s2 \<in> \<U>" "ext s1 = ext s2"
  shows "s1 = s2"
  using assms ext_neq_s by auto

lemma (in universe) ext_inserta0:
  assumes "a \<in> \<U>" "A \<subseteq> \<U>" "ext a \<in> ext ` A"
  shows "a \<in> A"
proof - 
  obtain x where x: "x \<in> A" "ext a = ext x"
    using assms by auto
  then have "a = x" 
    using ext_eq x(2) assms(1) assms(2) by auto 
  thus ?thesis using x(1) by auto
qed

lemma (in universe) ext_inserta:
  assumes "a \<in> \<U>" "A \<subseteq> \<U>" "a \<notin> A"
  shows "(ext a) \<notin> (ext ` A)" 
  using ext_inserta0 assms by auto
end

subsubsection \<open>Properties of bow operator\<close>
context universe
begin

lemma (in universe) bow_mono:
  assumes "A \<subseteq> B"
  shows   "\<bowtie> A \<subseteq> \<bowtie> B"
  using assms pcart_mono bow_def
  by (simp add: image_mono)

text \<open>Definition 4.1 (induction base)\<close>
(* {def:sd_prod} *)
lemma (in universe) bow_zero: "\<bowtie>{} = {{}}"
  using bow_def pcart_zero by auto

text \<open>Definition 4.1 (induction hypothesis)\<close>
(* {def:sd_prod} *)
lemma bow_insert: 
  assumes "a \<in> \<U>" "A \<subseteq> \<U>" "a \<notin> A"
  shows "\<bowtie> (insert a A) = \<bowtie> A \<union> {insert x y |x y. x \<in> ext a \<and> y \<in> \<bowtie> A}"
proof - 
  have "\<bowtie> (insert a A) = pcart (insert (ext a) (ext ` A))"
    using Set.image_insert bow_def by auto
  then have "pcart (insert (ext a) (ext ` A)) = pcart (ext ` A) \<union> 
                {insert x y |x y. x \<in> ext a \<and> y \<in> pcart (ext ` A)}"
    using pcart_insert ext_inserta assms by auto
  thus ?thesis using bow_def by auto
qed

lemma (in universe) bow_sg: 
  assumes "s \<in> \<U>"
  shows "\<bowtie>{s} = {{}} \<union> {{x}| x. x \<in> ext s}"
    using bow_insert bow_zero assms by auto 

lemma (in universe) bow_zero_mono: 
  assumes "T \<subseteq> \<U>"
  shows "{} \<in> \<bowtie>T"
  using bow_insert bow_zero bow_mono assms
  by force
end

context universe
begin

subsubsection \<open>Proposition 4.3.2\<close>
lemma (in universe) sdprod_s_in_T: 
  assumes "T \<subseteq> \<U>" "s \<in> T"
  shows "\<bowtie>{s} \<inter> \<bowtie>T = \<bowtie>{s}"
proof-
  from assms obtain T' where T': "T' = T - {s}" by auto
  then show ?thesis
  proof (cases "T'={}")
    case True
    then show ?thesis using True assms
      by (metis Int_absorb T' insert_Diff) 
  next
    case False
    then show ?thesis
      using assms(2) bot.extremum bow_mono inf.orderE insert_subsetI by blast
  qed
qed 

(*
text \<open>Proposition 4.5.2\<close>
lemma (in universe) sdprod_distr_int:
  assumes "T\<^sub>1 \<subseteq> \<U>" "T\<^sub>2 \<subseteq> \<U>"
  shows "\<bowtie>(T\<^sub>1 \<inter> T\<^sub>2) = \<bowtie>T\<^sub>1 \<inter> \<bowtie>T\<^sub>2"
proof - 
  have T1_fin: "T\<^sub>1 \<in> Fin" using assms U_fin rev_finite_subset Fin_is_finite by blast  
  have T2_fin: "T\<^sub>2 \<in> Fin" using assms U_fin rev_finite_subset Fin_is_finite by blast
  show ?thesis
    using T1_fin T2_fin
  proof (induct T\<^sub>1)
    case emptyI
    then show ?case using emptyI bow_zero bow_mono by force 
  next
    case (insertI A a)
    then show ?case 
    proof (cases "a \<in> A")
      case True
      then show ?thesis
        by (simp add: insertI.hyps(2) insertI.prems insert_absorb) 
    next
      case False
      then show ?thesis
      proof (cases "a \<in> T\<^sub>2")
        case True
        have f1: "insert a A \<inter> T\<^sub>2 = insert a (A \<inter> T\<^sub>2)"
          by (simp add: True)
        have "a \<in> \<U>"
          using assms True by auto
        then have f2: "\<bowtie> (insert a A) = 
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
    qed
  qed
qed
*)
end

end (* theory DDVUniverse*)
