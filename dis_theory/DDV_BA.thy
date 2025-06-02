(*  Title:      DDV_BA.thy
    Author:     Alicia Marinache
    Date:       June 7, 2024
    Modified:   June 14, 2024
*)

section \<open>Domain Data View Boolean Algebra\<close>

text \<open>The DomainDataView theory is built on top of a cylindric algebra, which, in turn, 
      is built on top of a Boolean Algebra. In this section, we define the DDV Boolean Algebra 
      theory \<open>DDV_BA\<close> and describe its properties.\<close>

theory DDV_BA
  imports 
    DDVUniverse
    "HOL.Boolean_Algebras"
    "HOL-Algebra.Group"
begin
locale ddv_ba = universe + 
  assumes a_in_SD: "\<And>a::sdata. a \<subseteq> SD"
begin

subsection \<open>Boolean Algebra Operators: Definitions\<close>
text \<open>DDV Boolean algebra operators: plus, star, zero, one, and complements\<close>
definition plus :: "sdata \<Rightarrow> sdata \<Rightarrow> sdata" (infixl "\<^bold>+"  80) where
  "a \<^bold>+ b = a \<union> b"
definition star :: "sdata \<Rightarrow> sdata \<Rightarrow> sdata" (infixl "\<^bold>*" 70) where
  "a \<^bold>* b = a \<inter> b"
definition zero :: "sdata" ("\<^bold>0") where
  "\<^bold>0 = {}"

definition one :: "sdata" ("\<^bold>1") where
  "\<^bold>1 = SD"
definition compl :: "sdata \<Rightarrow> sdata" ("\<^bold>-") where
  "\<^bold>-a = \<^bold>1 - a"

definition carrier_set :: "sdata set" ("A\<^sub>A") where
    "A\<^sub>A \<equiv> Pow SD"

lemma (in ddv_ba) dt_in_SD: "dt \<in> SD \<Longrightarrow> {dt} \<in> A\<^sub>A"
  using carrier_set_def by auto
end (* locale ddv_ba definition *)

subsection \<open>Boolean Algebra Operators: Properties\<close>
subsubsection \<open>Properties of closure on carrier set\<close>
context ddv_ba
begin
lemma (in ddv_ba)  one_closed: "\<^bold>1 \<in> A\<^sub>A"
  by (simp add: carrier_set_def local.one_def)

lemma (in ddv_ba) a_in_one: 
  assumes "a \<in> A\<^sub>A"
    shows "a \<subseteq> \<^bold>1"
  using assms one_def carrier_set_def by auto

lemma (in ddv_ba) a_in_one0: "a \<subseteq> \<^bold>1"
  using a_in_SD a_in_one one_def by auto

lemma (in ddv_ba) compl_closed: 
  assumes "a \<in> A\<^sub>A" 
  shows "\<^bold>-a \<in> A\<^sub>A"
  using assms carrier_set_def compl_def one_def by auto

lemma (in ddv_ba) plus_closed: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A"
  shows "a \<^bold>+ b \<in> A\<^sub>A"
  using assms a_in_one carrier_set_def one_def plus_def by auto

lemma (in ddv_ba) zero_closed: "\<^bold>0 \<in> A\<^sub>A"
  using zero_def carrier_set_def by auto

lemma (in ddv_ba) star_closed: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A"
  shows "a \<^bold>* b \<in> A\<^sub>A"
  using assms a_in_one carrier_set_def one_def star_def by auto
end (* \<open>Properties of closure on carrier set\<close> *)

subsubsection \<open>Properties of plus operator\<close>
context ddv_ba
begin
lemma (in ddv_ba) plus_comm: "a \<^bold>+ b = b \<^bold>+ a"
  by (simp add: Un_commute plus_def)

lemma (in ddv_ba) plus_assoc: "a \<^bold>+ (b \<^bold>+ c) = (a \<^bold>+ b) \<^bold>+ c"
  by (simp add: Un_assoc plus_def) 

lemma (in ddv_ba) plus_zero_r: "a \<^bold>+ \<^bold>0 = a"
  by (simp add: plus_def zero_def)

lemma (in ddv_ba) plus_zero_l: "\<^bold>0 \<^bold>+ a = a"
  by (simp add: plus_def zero_def)

lemma (in ddv_ba) plus_one_r: 
  assumes "a \<in> A\<^sub>A" 
  shows "a \<^bold>+ \<^bold>1 = \<^bold>1"
  using assms one_def carrier_set_def plus_def by auto
end (* \<open>Properties of plus operator\<close> *)

subsubsection \<open>Properties of star operator\<close>
context ddv_ba
begin
lemma (in ddv_ba) star_comm: "a \<^bold>* b = b \<^bold>* a"
  by (simp add: Int_commute star_def)

lemma (in ddv_ba) star_assoc: "a \<^bold>* (b \<^bold>* c) = (a \<^bold>* b) \<^bold>* c"
  by (simp add: Int_assoc star_def) 

lemma (in ddv_ba) star_one_r: 
  assumes "a \<in> A\<^sub>A"
  shows "a \<^bold>* \<^bold>1 = a"
  using assms one_def star_def carrier_set_def by auto

lemma (in ddv_ba) star_one_l: 
  assumes "a \<in> A\<^sub>A"
  shows "\<^bold>1 \<^bold>* a = a"
  using assms star_one_r star_comm by auto

lemma (in ddv_ba) star_zero_r: "a \<^bold>* \<^bold>0 = \<^bold>0"
  by (simp add: star_def zero_def)

end (* \<open>Properties of star operator\<close> *)

subsubsection \<open>Properties of distributivity of plus/star operators over each other\<close>
context ddv_ba
begin

lemma (in ddv_ba) plus_distr_star: "c \<^bold>* (a \<^bold>+ b) = (c \<^bold>* a) \<^bold>+ (c \<^bold>* b)"
  by (simp add: Int_Un_distrib plus_def star_def)
lemma (in ddv_ba) plus_distr_star2: "(a \<^bold>+ b) \<^bold>* c = (a \<^bold>* c) \<^bold>+ (b \<^bold>* c)"
  by (simp add: Int_Un_distrib2 plus_def star_def)

lemma (in ddv_ba) star_distr_plus: "c \<^bold>+ (a \<^bold>* b)  = (c \<^bold>+ a) \<^bold>* (c \<^bold>+ b)"
  by (simp add: Un_Int_distrib plus_def star_def)
lemma (in ddv_ba) star_distr_plus2: "(a \<^bold>* b) \<^bold>+ c = (a \<^bold>+ c) \<^bold>* (b \<^bold>+ c)"
  by (simp add: Un_Int_distrib2 plus_def star_def)

end (* \<open>Properties of distributivity of plus/star operators over each other\<close> *)

subsubsection \<open>Properties of complement operator\<close>
context ddv_ba
begin
lemma (in ddv_ba) complement_star: "a \<^bold>* \<^bold>-a = \<^bold>0"
  using star_def compl_def zero_def by simp 

lemma (in ddv_ba) complement_plus: 
  assumes "a \<in> A\<^sub>A"
  shows "a \<^bold>+ \<^bold>-a = \<^bold>1"
  using assms plus_def compl_def one_def a_in_one plus_one_r by auto 

lemma (in ddv_ba) complement_plus0: "a \<^bold>+ \<^bold>-a = \<^bold>1"
  using complement_plus a_in_SD carrier_set_def one_def by auto

end (* \<open>Properties of complement operator\<close> *)

subsection \<open>DDV Boolean Algebra: Properties\<close>
subsubsection \<open>Two monoids within the DDV\<close>
context ddv_ba
begin
interpretation plus_monoid: comm_monoid "\<lparr>carrier = A\<^sub>A, mult = (\<^bold>+), one = \<^bold>0\<rparr>"
  apply unfold_locales
  \<comment> \<open>Carrier set is closed over Plus\<close>
  apply (simp add: plus_closed)
  \<comment> \<open>Plus is associative\<close>
  apply (simp add: plus_assoc)
  \<comment> \<open>Zero is in the carrier set\<close>
  apply (simp add: zero_closed)
  \<comment> \<open>Zero is neutral element for plus\<close>
  apply (simp add: plus_zero_l)
  apply (simp add: plus_zero_r)
  \<comment> \<open>Plus is commutative\<close>
  apply (simp add: plus_comm)
  done

interpretation star_monoid: comm_monoid "\<lparr>carrier = A\<^sub>A, mult = (\<^bold>*), one = \<^bold>1\<rparr>"
  apply unfold_locales
  \<comment> \<open>Carrier set is closed over Star\<close>
  apply (simp add: star_closed)
  \<comment> \<open>Star is associative\<close>
  apply (simp add: star_assoc)
  \<comment> \<open>One is in the carrier set\<close>
  apply (simp add: one_closed)
  \<comment> \<open>One is neutral elements for Star\<close>
  apply (simp add: star_one_l)
  apply (simp add: star_one_r)
  \<comment> \<open>Star is commutative\<close>
  apply (simp add: star_comm)
  done
end (* \<open>Two monoids within the DDV\<close> *)

subsubsection \<open>The DDV as a model for a Boolean algebra\<close>
context ddv_ba
begin

text \<open>The \<open>Isabelle/HOL\<close> Boolean algebra is using a few extra operators (substract and ordering). 
      In this section, we define them using the classic set definitions, and 
      we show some of their properties, to be used by Boolean algebra interpretation proof)\<close>
definition minus :: "sdata \<Rightarrow> sdata \<Rightarrow> sdata" (infixl "\<setminus>\<^sub>A" 80) where
  "a \<setminus>\<^sub>A b = a - b"
definition lesseq :: "sdata \<Rightarrow> sdata \<Rightarrow> bool" (infixl "\<le>\<^sub>A" 85) where
  "a \<le>\<^sub>A b = (a \<subseteq> b)"
definition less :: "sdata \<Rightarrow> sdata \<Rightarrow> bool" (infixl "<\<^sub>A" 85) where
  "a <\<^sub>A b = (a \<subset> b)"

lemma (in ddv_ba) leI: "a <\<^sub>A b = (a \<le>\<^sub>A b \<and> \<not> b \<le>\<^sub>A a)"
  using less_def lesseq_def
  by (simp add: dual_order.strict_iff_not) 
lemma (in ddv_ba) le_refl: "a \<le>\<^sub>A a"
  using lesseq_def by simp 
lemma (in ddv_ba) le_trans: 
  assumes "a \<le>\<^sub>A b" "b \<le>\<^sub>A c"
  shows "a \<le>\<^sub>A c"
  using assms lesseq_def by simp 
lemma (in ddv_ba) le_eq: 
  assumes "a \<le>\<^sub>A b" "b \<le>\<^sub>A a"
  shows "a = b"
  using assms lesseq_def by simp 

lemma (in ddv_ba) le_star: "(a \<^bold>* b) \<le>\<^sub>A a"
  using lesseq_def star_def by simp
lemma (in ddv_ba) le_star_trans: 
  assumes "a \<le>\<^sub>A b" "a \<le>\<^sub>A c"
  shows "a \<le>\<^sub>A (b \<^bold>* c)"
  using assms lesseq_def star_def by auto

lemma (in ddv_ba) complement_minus: 
  assumes "a \<in> A\<^sub>A" "b \<in> A\<^sub>A"
  shows "a \<setminus>\<^sub>A b = a \<^bold>* \<^bold>-b"
  using assms minus_def star_def compl_def a_in_one by force

lemma (in ddv_ba) complement_minus0: 
  shows "a \<setminus>\<^sub>A b = a \<^bold>* \<^bold>-b"
  using complement_minus a_in_SD carrier_set_def by auto

interpretation boolean_algebra "(\<setminus>\<^sub>A)" "(\<^bold>-)" "(\<^bold>*)" "(\<le>\<^sub>A)" "(<\<^sub>A)" "(\<^bold>+)" "\<^bold>0" "\<^bold>1" 
  apply unfold_locales
                 apply (simp add: leI)
                apply (simp add: lesseq_def)
               apply (simp add: lesseq_def)
              apply (simp add: lesseq_def)
             apply (simp add: lesseq_def star_def)
            apply (simp add: lesseq_def star_def)
           apply (simp add: lesseq_def star_def)
          apply (simp add: lesseq_def plus_def)
         apply (simp add: lesseq_def plus_def)
        apply (simp add: lesseq_def plus_def)
       apply (simp add: lesseq_def zero_def)
      apply (simp add: lesseq_def a_in_one0)
     apply (simp add: star_distr_plus)
    apply (simp add: complement_star)
   apply (simp add: complement_plus0)
  apply (simp add: complement_minus0)
  done

interpretation abstract_boolean_algebra "(\<^bold>*)" "(\<^bold>+)" "(\<^bold>-)" "\<^bold>0" "\<^bold>1"
  by (simp add: local.boolean_algebra.abstract_boolean_algebra_axioms)
end (* \<open>The DDV is a Boolean algebra\<close> *)

end