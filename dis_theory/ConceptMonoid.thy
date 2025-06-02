(*  Title:      ConceptMonoid.thy
    Author:     Alicia Marinache
    Date:       April 7, 2022
    Modified:   June 13, 2024
*)

section \<open>Concept Monoid\<close>

text \<open>To achieve the transformation from data to information and further to knowledge,
we need to give meaning to the data, specifically to its sorts (or attributes). Thus we take
the sorts of the dataset and consider them in a specific context. We call this context the
domain of application for the data, and within it we capture the relevant concepts.\<close>

text \<open>The ConceptMonoid theory describes the DIS monoid of concepts.\<close>

theory ConceptMonoid
  imports 
    Concept
    "HOL-Algebra.Group"
begin

text \<open>A set of concepts \<open>C\<close>, with \<open>\<oplus>\<^sub>C\<close> and \<open>e\<^sub>C\<close> are syntactically equivalent to the \<open>monoid\<close> structure defined in HOL-Algebra.Group. The term "\<open>\<C> C\<close>" is an abbreviation for the \<open>monoid\<close> structure.\<close>

abbreviation plus_monoid :: "'a concept set \<Rightarrow> 'a concept monoid" ("\<C>")
  where "plus_monoid C \<equiv> \<lparr>carrier = C, mult = (\<oplus>\<^sub>C), one = e\<^sub>C\<rparr>"

text \<open>A set of atomic concepts (or atoms), together with the composition operator and the empty 
concept, form a monoid of concepts, described below with the \<^term>\<open>concept_monoid\<close> locale. 
The set of atoms correspond to attributes of dataset(s) or to notions found in the domain of 
application, therefore it is assumed to be finite and non-empty. The carrier set \<open>C\<close> of the monoid 
is built as the \<open>\<oplus>\<^sub>C\<close> closure over the set of atoms \<open>At\<close>, which is the parameter of the 
\<^term>\<open>concept_monoid\<close> locale. 
In addition, the empty concept \<open>e\<^sub>C\<close> is assumed to be part of the carrier set.\<close>

locale concept_monoid = 
  fixes At :: "'a concept set"
  assumes atoms_not_empty: "At \<noteq> {}" 
  assumes atoms_finite: "finite At"

begin

subsection \<open>Concept Monoid Operators: Definitions\<close>
text \<open>The carrier set of the monoid of concepts is the closure of oplus operator over the set of atoms. \<close>

definition C :: "'a concept set"
  where "C \<equiv> oplus_closure At \<union> {e\<^sub>C}"

end (* locale concept_monoid *)

subsection \<open>Concept Monoid Operators: Properties\<close>
subsubsection \<open>Properties of the composition operator\<close>
context concept_monoid
begin
text \<open>We prove two basic properties of the monoid of concepts, that \<open>e\<^sub>C\<close> is its  neutral element, 
both to the left and right.\<close>

lemma (in concept_monoid) zero_l: "\<And>x. x \<in> C \<Longrightarrow> e\<^sub>C \<oplus>\<^sub>C x = x"
  by (simp add: zero_def oplus_def)

lemma (in concept_monoid) zero_r: "\<And>x. x \<in> C \<Longrightarrow> x \<oplus>\<^sub>C e\<^sub>C = x"
  by (simp add: zero_r0)

text \<open>Within the \<open>concept_monoid\<close>, \<open>\<oplus>\<^sub>C\<close> is closed over the carrier set \<open>C\<close>.\<close>

lemma (in concept_monoid) oplus_closed: "\<And>x y. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<oplus>\<^sub>C y \<in> C"
  by (metis C_def UnE UnI1 oplus_closure.intros(2) oplus_comm singletonD zero_r)
end

subsection \<open>Concept Monoid: Properties\<close>
subsubsection \<open>Concept Monoid as a commutative monoid\<close>
context concept_monoid
begin
text \<open>We show that the structure \<open>"\<C> C"\<close> is a model of the \<open>comm_monoid\<close> structure, as described in HOL-Algebra.Group. Thus, all the theorems proved in the HOL commutative monoid theory are satisfied for the monoid of concepts of the DIS.\<close>

interpretation comm_monoid "\<C> C" 
  apply unfold_locales
  \<comment> \<open>Composition is closed over the carrier set\<close>
  apply (simp add: oplus_closed)
  \<comment> \<open>Composition is associative\<close>
  apply (simp add: oplus_assoc)
  \<comment> \<open>Empty concept is in the carrier set\<close>
  apply (simp add: C_def)
  \<comment> \<open>Empty concept is neutral over the composition\<close>
  apply (simp add: zero_l)
  apply (simp add: zero_r)
  \<comment> \<open>Composition is commutative\<close>
  apply (simp add: oplus_comm)
  done
end (* context concept_monoid *)

end (* theory ConceptMonoid *)

