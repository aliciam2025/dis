(*  Title:      DomainOnt.thy
    Author:     Alicia Marinache
    Date:       June 20, 2022
    Modified:   June 12, 2024
*)

section \<open>Domain Ontology\<close>

text \<open>Recall that the Domain Ontology component of a DIS is formed of a monoid of concepts, 
a Boolean lattice (in which the atoms correspond to the attributes of the dataset under consideration), 
and a family of graphs all rooted in the Boolean lattice. The \<^term>\<open>DomainOnt\<close> theory encompasses 
this mathematical structure.\<close>

theory DomainOnt
  imports 
    ConceptMonoid
    ConceptLattice
    ConceptRootGraph

begin

text \<open>The \<^term>\<open>domain_ontology\<close> instantiates three parameters: (i) the concepts monoid given by its
set of atoms \<open>A\<^sub>C\<close>, (ii) the concepts Boolean lattice \<^term>\<open>concept_lattice\<close>, 
given by its sets of atoms \<open>A\<^sub>L\<close>, and (iii) the family (set) of rooted graphs. We impose the DIS 
Domain Ontology axioms: the set of lattice atoms is a subset of the monoid atoms, the roots of each graph 
are in the lattice, and the vertices of each graph are a subset of the monoid carrier set.\<close>

locale domain_ontology = 
  cmonoid: concept_monoid where At = A\<^sub>C + 
  clattice: concept_lattice where At = A\<^sub>L +
  cgraphs: family_root_graphs where \<G> = \<G>

 for   A\<^sub>C :: "'a concept set"
   and A\<^sub>L :: "'a concept set"
   and \<G> ::  "'a rgraph set" + 
assumes
      atomsL_in_C: "A\<^sub>L \<subseteq> A\<^sub>C"
  and graph_roots_in_L: "\<And> g. g \<in> \<G> \<longrightarrow> t\<^sub>g \<in> clattice.L"
  and graph_carriers_in_C: "\<And> g. g \<in> \<G> \<longrightarrow> V\<^sub>g \<subseteq> cmonoid.C" 
begin
print_locale! domain_ontology
end

end (* theory DomainOnt *)
