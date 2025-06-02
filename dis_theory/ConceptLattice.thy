(*  Title:      ConceptLattice.thy
    Author:     Alicia Marinache
    Date:       April 7, 2022
    Modified:   June 13, 2024
*)

section \<open>Concept Lattice\<close>

text\<open>The ConceptLattice theory describes the DIS Boolean lattice of concepts. 
We begin the construction of a new DIS from an existing dataset, which guides the design of the 
core component of the domain ontology (its Boolean lattice of concepts). 
The attributes in the dataset schema correspond one-to-one to the atoms of the Boolean lattice. 
We take a subset of these atoms and use the \<open>partOf\<close> relation to generate a free Boolean lattice over it. 
By the construction of the lattice, the task of mapping the data to the ontology becomes trivial, 
as the attributes of the data view schema have a one-to-one correspondence to the atoms of the Boolean lattice.\<close>

theory ConceptLattice
  imports 
   Concept
   "HOL.Boolean_Algebras"
   "HOL-Algebra.Group"

begin

text \<open>A lattice can be represented as a relational structure (a carrier set and a partial order with certain properties) 
or as an algebraic structure (a carrier set, two binary operators, meet and join, one unary operator, complement, 
and two constants, the neutral elements for the two binary operators, respectively). 
The two representations are equivalent, and in our work we use the terms \<open>Boolean lattice\<close> and \<open>Boolean algebra\<close> interchangeably. \<close>

text \<open>The other two elements of the Boolean lattice, its unary operator (complement) and the \<open>\<otimes>\<^sub>C\<close> 
      neutral element (top), can only be defined w.r.t. the carrier set of the lattice. 
      Thus, we need to separate the declaration of the \<^term>\<open>concept_lattice\<close> into two locales. 
      within the \<^term>\<open>concept_lattice0\<close> we define the lattice operators and its carrier set, 
      and within the \<^term>\<open>concept_lattice\<close> we show it is a Boolean lattice (algebra).\<close>

subsection \<open>Concept Lattice: the base\<close>
text \<open>From a given set of atoms we can form a lattice of concepts. 
In it, the \<open>\<oplus>\<^sub>C\<close> and \<open>\<otimes>\<^sub>C\<close> correspond to the join and meet of a lattice, respectively. The  empty concept \<open>e\<^sub>C\<close>
is its bottom, and its top will be defined as the composition of all the atoms. Similar to the monoid 
structure, the carrier set \<open>L\<close> of the lattice is built as the \<open>\<oplus>\<^sub>C\<close> closure over the atomic set of concepts \<open>At\<close>, 
given as the parameter of the \<^term>\<open>concept_lattice0\<close> locale. 
In addition, the empty concept \<open>e\<^sub>C\<close> is assumed to be part of the carrier set.\<close>

locale concept_lattice0 = 
  \<comment> \<open>\<^term>\<open>concept_lattice0\<close> parameters, the set of lattice atoms\<close>
  fixes At :: "'a concept set"
  assumes atoms_not_empty: "At \<noteq> {}"
begin

subsubsection \<open>Concept Lattice Operators: Definitions\<close>
definition L :: "'a concept set"
  where "L \<equiv> oplus_closure At \<union> {e\<^sub>C}"

text \<open>With concepts as sets, the composition operator dual \<open>\<otimes>\<^sub>C\<close> is the intersection of sets.\<close>
text \<open>Definition 4.22\<close> (* {def:blat_star} *)
definition otimes :: "'a concept \<Rightarrow> 'a concept \<Rightarrow> 'a concept" (infixl "\<otimes>\<^sub>C" 65)
  where "c1 \<otimes>\<^sub>C c2 = (c1 \<inter> c2)"

text \<open>Definition 4.23\<close> (* {def:blat_one} *)
definition topL :: "'a concept" ("\<top>\<^sub>L")
  where "\<top>\<^sub>L = \<Union>{c. c\<in> At}"

text \<open>Definition 4.24\<close> (* {def:blat_compl} *)
definition complL :: "'a concept \<Rightarrow> 'a concept" ("\<ominus>\<^sub>L _" [81] 80)
  where "\<ominus>\<^sub>L c = \<Union>{u. u \<in> At \<longrightarrow> \<not>(u \<sqsubseteq>\<^sub>C c)}"

end (* locale concept_lattice0 *)

subsubsection \<open>Concept Lattice Operators: Properties\<close>
context concept_lattice0
begin
text \<open>Basic properties of \<open>\<otimes>\<^sub>C\<close>: commutative, associative\<close>

lemma (in concept_lattice0) otimes_comm: "c1 \<otimes>\<^sub>C c2 = c2 \<otimes>\<^sub>C c1"
  by (simp add: otimes_def inf_commute)

lemma (in concept_lattice0) otimes_assoc: "(c1 \<otimes>\<^sub>C c2) \<otimes>\<^sub>C c3 = c1 \<otimes>\<^sub>C (c2 \<otimes>\<^sub>C c3)"
  by (simp add: otimes_def inf_assoc)

text \<open>The two binary operators distribute over each other\<close>

lemma (in concept_lattice0) oplus_distr_otimes: "c1 \<oplus>\<^sub>C (c2 \<otimes>\<^sub>C c3) = (c1 \<oplus>\<^sub>C c2) \<otimes>\<^sub>C (c1 \<oplus>\<^sub>C c3)"
  by (simp add: oplus_def otimes_def sup_inf_distrib1)

lemma (in concept_lattice0) otimes_distr_oplus: "c1 \<otimes>\<^sub>C (c2 \<oplus>\<^sub>C c3) = (c1 \<otimes>\<^sub>C c2) \<oplus>\<^sub>C (c1 \<otimes>\<^sub>C c3)"
  by (simp add: otimes_def oplus_def inf_sup_distrib1)
end (* \<open>Concept Lattice Operators: Properties\<close> *)

subsection \<open>Concept Lattice as a Boolean algebra\<close>
locale concept_lattice = concept_lattice0 + 
  assumes top_r: "\<And>c. c \<otimes>\<^sub>C \<top>\<^sub>L = c"
      and top_inL: "\<top>\<^sub>L \<in> L"
      and otimes_closed_L: "\<And>x y. x \<in> L \<Longrightarrow> y \<in> L \<Longrightarrow> x \<otimes>\<^sub>C y \<in> L"
      and otimes_cancel_r: "\<And>x. x \<otimes>\<^sub>C \<ominus>\<^sub>L x = e\<^sub>C"
      and oplus_cancel_r: "\<And>x. x \<oplus>\<^sub>C \<ominus>\<^sub>L x = \<top>\<^sub>L"
begin
end (* locale concept_lattice *)

subsubsection \<open>Concept Lattice Operators: Properties\<close>
context concept_lattice
begin 
text \<open>The basic properties of \<open>e\<^sub>C\<close> within the lattice of concepts: neutral to the left and right.\<close>

lemma (in concept_lattice) zero_inL: "e\<^sub>C \<in> L"
  by (simp add: L_def)

lemma (in concept_lattice) zero_l: "\<lbrakk>c \<in> L\<rbrakk> \<Longrightarrow> e\<^sub>C \<oplus>\<^sub>C c = c"
  by (simp add: zero_def oplus_def)

text \<open>Within the \<open>concept_lattice\<close>, \<open>\<oplus>\<^sub>C\<close> is closed over the carrier set \<open>L\<close>.\<close>

lemma (in concept_lattice) oplus_closed_L: "\<And>x y. x \<in> L \<Longrightarrow> y \<in> L \<Longrightarrow> x \<oplus>\<^sub>C y \<in> L"
  by (metis L_def UnE UnI1 concept_lattice.zero_l concept_lattice_axioms oplus_closure.intros(2) singleton_iff zero_r0)

text \<open>Proprties of the \<open>partOf\<close> relationship in the context of \<open>concept_lattice\<close>.\<close>

lemma (in concept_lattice) partOf_trans: 
    "\<And>x y z. x \<in> L \<Longrightarrow> y \<in> L \<Longrightarrow> z \<in> L \<Longrightarrow> x \<sqsubseteq>\<^sub>C y \<Longrightarrow> y \<sqsubseteq>\<^sub>C z \<Longrightarrow> x \<sqsubseteq>\<^sub>C z"
  by (simp add: partOf_def)

lemma (in concept_lattice) partOf_oplus: "\<And>x y. x \<in> L \<Longrightarrow> y \<in> L \<Longrightarrow> x \<sqsubseteq>\<^sub>C (x \<oplus>\<^sub>C y)"
  unfolding partOf_def oplus_def
  by auto

lemma (in concept_lattice) partOf_times: "\<And>x y. x \<in> L \<Longrightarrow> y \<in> L \<Longrightarrow> (x \<otimes>\<^sub>C y) \<sqsubseteq>\<^sub>C x"
  unfolding partOf_def otimes_def
  by auto

text \<open>The basic property of \<open>\<top>\<^sub>L\<close> within the lattice of concepts: neutral to the left.\<close>

lemma (in concept_lattice) top_l: "\<lbrakk>c \<in> L\<rbrakk> \<Longrightarrow> \<top>\<^sub>L \<otimes>\<^sub>C c = c"
  by (simp add: top_r otimes_comm) 

end (* \<open>Concept Lattice Operators: Properties\<close> *)

subsubsection \<open>Concept Lattice as a dual abelian mondoid\<close>
context concept_lattice
begin 

text \<open>The lattice is a dual abelian monoid: one over composition and empty concept, and one over 
their dual operators, \<open>\<otimes>\<^sub>C\<close> and \<open>\<top>\<^sub>L\<close>.\<close>

interpretation plus_monoidL: comm_monoid "\<lparr>carrier = L, mult = (\<oplus>\<^sub>C), one = e\<^sub>C\<rparr>"
  apply unfold_locales
  \<comment> \<open>Composition is closed over the carrier set\<close>
  apply (simp add: oplus_closed_L)
  \<comment> \<open>Composition is associative\<close>
  apply (simp add: oplus_assoc)
  \<comment> \<open>Empty concept is in the carrier set\<close>
  apply (simp add: zero_inL)
  \<comment> \<open>Empty concept is neutral over the composition\<close>
  apply (simp add: zero_l)
  apply (simp add: zero_r0)
  \<comment> \<open>Composition is commutative\<close>
  apply (simp add: oplus_comm)
  done

interpretation mult_monoidL: comm_monoid "\<lparr>carrier = L, mult = (\<otimes>\<^sub>C), one = \<top>\<^sub>L\<rparr>"
  apply unfold_locales
  \<comment> \<open>Composition is closed over the carrier set\<close>
  apply (simp add: otimes_closed_L)
  \<comment> \<open>Composition is associative\<close>
  apply (simp add: otimes_assoc)
  \<comment> \<open>Empty concept is in the carrier set\<close>
  apply (simp add: top_inL)
  \<comment> \<open>Empty concept is neutral over the composition\<close>
  apply (simp add: top_l)
  apply (simp add: top_r)
  \<comment> \<open>Composition is commutative\<close>
  apply (simp add: otimes_comm)
  done

end (* \<open>Concept Lattice as a dual abelian mondoid\<close> *)

subsubsection \<open>Concept Lattice as a Boolean algebra\<close>
context concept_lattice
begin 
text \<open>In addition, \<open>L\<close> together with its two binary operators, the unary operator, 
and the two neutral elements is a Boolean algebra, or it is a model for the \<open>abstract_boolean_algebra\<close>, as described in \<open>HOL.Boolean_Algebras\<close>. \<close>

interpretation abstract_boolean_algebra "(\<otimes>\<^sub>C)" "(\<oplus>\<^sub>C)" complL e\<^sub>C "\<top>\<^sub>L"
  apply unfold_locales
  \<comment> \<open>\<open>\<otimes>\<^sub>C\<close> and \<open>\<oplus>\<^sub>C\<close> properties: associative and commutative\<close>
  apply (simp add: otimes_assoc)
  apply (simp add: otimes_comm)
  apply (simp add: oplus_assoc)
  apply (simp add: oplus_comm)
  \<comment> \<open>\<open>\<otimes>\<^sub>C\<close> and \<open>\<oplus>\<^sub>C\<close> distribute over each other\<close>
  apply (simp add: otimes_distr_oplus)
  apply (simp add: oplus_distr_otimes)
  \<comment> \<open>Top and bottom (zero) are neutral elements\<close>
  apply (simp add: top_r)
  apply (simp add: zero_r0)
  \<comment> \<open>Complement cancels over \<open>\<otimes>\<^sub>C\<close> and \<open>\<oplus>\<^sub>C\<close>\<close>
  apply (simp add: otimes_cancel_r)
  apply (simp add: oplus_cancel_r)
  done

end (* \<open>Concept Lattice as a Boolean algebra\<close> *)

end (* theory ConceptLattice *)

