(*  Title:      ConceptRootGraph.thy
    Author:     Alicia Marinache
    Date:       April 7, 2022
    Modified:   June 13, 2024
*)

section \<open>Concept Rooted Graph\<close>

text \<open>Recall that in a DIS, we start by considering the sorts of the dataset to be a subset of 
the concepts of the domain.We then ask domain experts to capture other concepts that are deemed 
significant to the domain of application and that are not part of the Boolean lattice. These concepts 
are captured from the domain of knowledge or from an existing ontology as rooted graphs. A rooted 
graph is an acyclick directed graph, with a distinguished element, the root. The root is a unique 
concept (vertice) of the graph which is reachable from any other vertice.\<close>

text \<open>Theory ConceptRootGraph describes such a rooted graph, using the directed graph theory Digraph 
authored by Noschinski and Neumann.\<close>

theory ConceptRootGraph
  imports 
   Concept
   Digraph
   "HOL.Transitive_Closure"
begin

subsection \<open>Concept Rooted Graph: Definitions\<close>
text \<open>In DIS, we need to declare a family of rooted graphs. As such, the rooted graphs are defined 
with the use of an Isabelle/HOL \<^term>\<open>record\<close>. A record is a complex datatype, defined as an 
extensible n-tuple. The record's fields (components) have names by which they can be accessed. 
Records and their fields make expressions easier to read and reduce the risk of confusing one field
for another. As a complex datatype, one can declare a set of records (unlike a "set of locales").\<close>

text \<open>The record \<open>rgraph\<close> has three components: the vertices \<open>V\<close>, a set of concepts, the edges \<open>R\<close>, 
a set of pairs of concepts, and the root \<open>t\<close>, a concept. All three components are indexable, and marked 
as such with the \<open>\<index>\<close> symbol. This will allow one to declare two graphs, \<open>G\<close> and \<open>H\<close>, and use the 
terms \<^term>\<open>V\<^sub>G\<close>, \<^term>\<open>V\<^sub>H\<close> to refer to the vertices components on the graph \<open>G\<close>, respectively \<open>H\<close>. 
With this understanding, we define two operators, tail and head, to mimic the \<^term>\<open>pre_digraph\<close> 
record components. The operator tail gives access to the tail of a given edge (or the first element 
of the edge pair), while the operator head gives access to the head of it (or the 2nd element of the 
edge pair).\<close>

type_synonym 'a edge = "'a concept \<times> 'a concept"

record 'a rgraph = 
  vertices :: "'a concept set" ("V\<index>")
  edges :: "'a edge set" ("R\<index>")
  root :: "'a concept" ("t\<index>")

definition tail :: "'a edge \<Rightarrow> 'a concept"
  where "tail e = fst e"

definition head :: "'a edge \<Rightarrow> 'a concept"
  where "head e = snd e"

\<comment> \<open>Pre-defined relation (edge) properties: transitivity, reflexitivity, and reflexive-transitivity. 
More properties can be defined in extensions of the ConceptRootGraph.\<close>
definition is_trans :: "'a edge set \<Rightarrow> bool"
  where "is_trans E \<equiv> trancl E = E"

definition is_refl :: "'a edge set \<Rightarrow> bool" 
  where "is_refl E \<equiv> reflcl E = E"

definition is_refltr :: "'a edge set \<Rightarrow> bool" 
  where "is_refltr E \<equiv> rtrancl E = E"

text \<open>The \<open>vertices\<close> and \<open>edges\<close> component of the record \<open>rgraph\<close> along with the two operators 
\<open>tail\<close> and \<open>head\<close> are syntactically equivalent to the \<open>pre_digraph\<close> record. The term "\<open>\<G>\<^sub>r G\<close>" 
is an abbreviation for the \<open>pre_digraph\<close> record.\<close>

abbreviation digraph :: "'a rgraph \<Rightarrow> ('a concept,'a edge) pre_digraph" ("\<G>\<^sub>r")
  where "digraph G  \<equiv> \<lparr>verts = V\<^bsub>G\<^esub>, arcs = R\<^bsub>G\<^esub>, tail = tail, head = head \<rparr>"

subsection \<open>Concept Rooted Graph\<close>
text \<open>A rooted graph is an acyclic directed graph that has a unique element (the root), reachable 
from every vertice in the graph. It is defined using the pre-existing \<^term>\<open>loopfree_digraph\<close> locale. 
It has only one parameter, the \<open>rgraph G\<^sub>r\<close> structure.\<close>

locale concept_root_graph = 
 dag: loopfree_digraph where G = "\<G>\<^sub>r G\<^sub>r"
for G\<^sub>r :: "'a rgraph"  (structure) + 
  assumes                        
        G_def: "G = \<G>\<^sub>r G\<^sub>r" 
    and lf_graph: "loopfree_digraph G"
    and R_def: "R \<subseteq> (C \<times> C)"
    and root_in_C: "t \<in> C"
    and root_reachable: "\<And>c. c \<in> C \<longrightarrow> c \<rightarrow>\<^sup>*\<^bsub>G\<^esub> t"
    and root_unique: "\<And>c. c \<rightarrow>\<^sup>*\<^bsub>G\<^esub> t' \<longrightarrow> t = t'"
begin
print_locale! concept_root_graph
end (* locale concept_root_graph *)

subsubsection \<open>Concept Rooted Graphs: Properties\<close>
text \<open>The concept rooted graph is acyclic\<close>

lemma (in concept_root_graph) loop_free: "(c1, c2) \<in> R \<Longrightarrow> c1 \<noteq> c2"
  using G_def by auto

subsection \<open>Family of Concept Rooted Graphs\<close>
text \<open>The family of rooted graphs is simply a set of \<^term>\<open>rgraph\<close> records, where each such a record 
is a \<open>concept_rooted_graph\<close> structure.\<close>

locale family_root_graphs = 
  fixes \<G> :: "'a rgraph set" 
  assumes \<G>_def: "\<And> g. g \<in> \<G> \<longrightarrow> concept_root_graph g"

end (* Theory ConceptRootGraph *)

