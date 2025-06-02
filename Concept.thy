(*  Title:      Concept.thy
    Author:     Alicia Marinache
    Date:       April 7, 2022
    Modified:   June 12, 2024
*)

text \<open>The DIS is a novel data-centered framework for knowledge representation. It consists
of a domain knowledge representation, called the domain ontology \<^term>\<open>\<O>\<close>, a domain data
representation, called the domain data view \<^term>\<open>\<A>\<close>, and an operator \<^term>\<open>\<tau>\<close> that  maps \<^term>\<open>A\<close>
to \<^term>\<open>\<O>\<close>. To define the domain ontology, we use a monoid of concepts \<^term>\<open>\<C>\<close>, a Boolean lattice
of concepts \<open>\<L>\<close>, and a family of rooted graphs \<^term>\<open>\<G>\<close>.\<close>

text \<open>In a DIS, the concepts in the domain ontology originate from two sources: 
(i) the data, and (ii) the domain of application. 
The concepts in the domain ontology can be composed to form new concepts. 
We understand the composition as the Cartesian construction of concepts. 
Similar to how the information in a dataset record is not dependant on the order of attributes 
in a dataset, we require the composition operator to be commutative (up to an isomorphism), 
associative, and idempotent. The commutativity and associativy properties ensure that the order 
in which concepts are composed is not relevant. The idempotency property ensures that by 
composing a concept with itself the system does not create a new concept, or new knowledge from
the existing knowledge in the system.\<close>

text\<open>In current approaches to connect an ontology to existing data, mapping the two components to each 
other is a time consuming task, as it needs to bridge the conceptual gap between the two layers. 
To close this conceptual gap between the domain representation and the data view, in DIS, 
the core component of the domain ontology \<^term>\<open>\<O>\<close> is built using the 
Cartesian \<^term>\<open>partOf\<close> relation. This is similar to the relation between elements of the data view. 
A concept with no sub-parts is called an \<open>atomic\<close> concept or an \<open>atom\<close>.\<close> 

section \<open>Concept\<close>

theory Concept
  imports 
    Main
begin

text \<open>The concept datatype is a set of atoms. The atoms are defined as a datatype on the 
      concrete DIS implementation.\<close>

type_synonym 'a concept = "'a set"

subsection \<open>Concept Operators: Definitions\<close>
text \<open>With concepts as sets, the empty concept \<open>e\<^sub>C\<close> is simply a notation for the empty set, 
the composition operator \<open>\<oplus>\<^sub>C\<close> a renaming of the set union operator, and the partial order \<open>\<sqsubseteq>\<^sub>C\<close> 
(or \<^term>\<open>partOf\<close> a renaming of the set inclusion relation.\<close>

text \<open>Definition 4.19\<close>
(* {def:blat_plus} *)
definition oplus :: "'a concept \<Rightarrow> 'a concept \<Rightarrow> 'a concept" (infixl "\<oplus>\<^sub>C" 75)
  where "c1 \<oplus>\<^sub>C c2 = (c1 \<union> c2)"

text \<open>Definition 4.20\<close>
(* {def:blat_zero} *)
definition zero :: "'a concept" ("e\<^sub>C")
  where "zero = {}"

text \<open>Definition 4.21\<close>
(* {def:blat_partof} *)
definition partOf :: "'a concept \<Rightarrow> 'a concept \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>C" 66)
  where "c1 \<sqsubseteq>\<^sub>C c2 = (c1 \<subseteq> c2)"

text \<open>Within a given set \<open>A\<close> of concepts, atomicity is defined using the \<open>partOf\<close> relationship\<close>

definition isAtom :: "'a concept \<Rightarrow> 'a concept set \<Rightarrow> bool"
  where "isAtom a A \<equiv> ((a \<in> A) \<and> \<not>(\<exists>x. x \<in> A \<and> x \<noteq> a \<and> x \<sqsubseteq>\<^sub>C a))"

definition atomSet :: "'a concept set \<Rightarrow> bool"
  where "atomSet A = (\<forall> x \<in> A. isAtom x A)"

text \<open>We give the definition of the closure of the \<open>\<oplus>\<^sub>C\<close> operator over a given set of concepts \<open>A\<close>, 
      as an inductive set.\<close>

inductive_set
  oplus_closure :: "'a concept set \<Rightarrow> 'a concept set"
  for A :: "'a concept set"
  where
      a_in_A:  "a \<in> A \<Longrightarrow> a \<in> oplus_closure A" 
    | ab_in_closure: "a \<in> oplus_closure A \<Longrightarrow> b \<in> oplus_closure A \<Longrightarrow> a \<oplus>\<^sub>C b \<in> oplus_closure A"

subsection \<open>Concept Operators: Properties\<close>
subsubsection \<open>Properties of composition operator\<close>
context 
begin
text \<open>We can prove some basic properties of the composition \<open>\<oplus>\<^sub>C\<close> operator, such as commutativity, 
associativity, and idempotency.\<close>

lemma oplus_comm: "c1 \<oplus>\<^sub>C c2 = c2 \<oplus>\<^sub>C c1"
  by (simp add: oplus_def sup_commute)

lemma oplus_assoc: "(c1 \<oplus>\<^sub>C c2) \<oplus>\<^sub>C c3 = c1 \<oplus>\<^sub>C (c2 \<oplus>\<^sub>C c3)"
  by (simp add: oplus_def sup_assoc)
  
lemma oplus_idempotent: "c \<oplus>\<^sub>C c = c"
  by (simp add: oplus_def)
end

subsubsection \<open>Properties of empty concept\<close>
context 
begin
text \<open>We can prove that the empty concept \<open>e\<^sub>C\<close> is a neutral element for the 
composition \<open>\<oplus>\<^sub>C\<close> operator, both to the right and the left.\<close>

lemma zero_r0: "\<And>x. x \<oplus>\<^sub>C e\<^sub>C = x"
  by (simp add: zero_def oplus_def)

lemma zero_l0: "\<And>x. e\<^sub>C \<oplus>\<^sub>C x = x"
  by (simp add: zero_def oplus_def)
end


end (* theory Concept *)