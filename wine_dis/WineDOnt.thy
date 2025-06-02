(*  Title:      WineDOnt.thy
    Author:     Alicia Marinache
    Date:       July 25, 2023
    Updated:    June 02, 2025
*)

section \<open>Wine Domain Ontology\<close>

text \<open>In the Wine Domain Ontology section, we implement the Domain Ontology theory. We start from 
      the dataset defined in the Domain Data View section, with the attributes \<open>grape\<close>, \<open>sugar\<close>, 
      \<open>body\<close>, and \<open>colour\<close>. In addition, other (atomic) concepts from the domain of application, 
      such as \<open>producer\<close> and \<open>region\<close> are captured by the domain experts. 
      The process of capturing the dataset attributes can be automated. The other concepts in the 
      domain of application are to  be defined manually by the ontology engineer(s), with assistance 
      from the domain experts.\<close>

theory WineDOnt
  imports  "../DIS/DomainOnt"
begin

 \<comment> \<open>The abstract  datatype for the Wine Ontology is \<open>wine\<^sub>a\<^sub>t\<close>, 
a collection of all atoms of the ontology.\<close>

datatype wine = grape\<^sub>a\<^sub>t | sugar\<^sub>a\<^sub>t | body\<^sub>a\<^sub>t | colour\<^sub>a\<^sub>t | 
                producer\<^sub>a\<^sub>t | region\<^sub>a\<^sub>t | estate\<^sub>a\<^sub>t 

 \<comment> \<open>The atoms of the \<^term>\<open>concept_lattice\<close>:\<close>

definition grape :: "wine concept" where "grape = {grape\<^sub>a\<^sub>t}"

definition sugar :: "wine concept" where "sugar = {sugar\<^sub>a\<^sub>t}"

definition body :: "wine concept"  where "body = {body\<^sub>a\<^sub>t}"

definition colour :: "wine concept" where "colour = {colour\<^sub>a\<^sub>t}"

definition wine :: "wine concept" 
  where "wine = grape \<oplus>\<^sub>C sugar \<oplus>\<^sub>C body \<oplus>\<^sub>C colour"

 \<comment> \<open>The other concepts in the domain of application, atoms of the \<^term>\<open>concept_monoid\<close>\<close>

definition producer :: "wine concept" where "producer = {producer\<^sub>a\<^sub>t}"

definition region :: "wine concept"   where "region = {region\<^sub>a\<^sub>t}"

definition estate :: "wine concept"   where "estate = {estate\<^sub>a\<^sub>t}"

definition A\<^sub>L :: "wine concept set" where
  "A\<^sub>L = {grape, sugar, body, colour}"

definition non_lattice_atoms :: "wine concept set"
  where "non_lattice_atoms = {producer, region, estate}"

definition A\<^sub>C :: "wine concept set"
  where "A\<^sub>C = A\<^sub>L \<union> non_lattice_atoms"

text \<open>The Wine Ontology \<open>wine_dont\<close> instantiates the \<^term>\<open>domain_ontology\<close> structure, taking two 
parameters: \<open>A\<^sub>C\<close> and \<open>A\<^sub>L\<close>, the sets of atoms over which the \<^term>\<open>concept_monoid\<close>, respectively 
 \<^term>\<open>concept_lattice\<close> are built. In addition, it instantiates the \<^term>\<open>concept_rooted_graph\<close> 
structure as a graph rooted at \<open>grape\<close>.\<close>

definition V\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s :: "wine concept set"
  where "V\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s = {producer, region, estate}"

definition R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s :: "wine edge set"
  where "R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s = {(region, estate), (producer, estate), (estate, grape)}"

definition G\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s :: "wine rgraph"
  where "G\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s = \<lparr>vertices = V\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s, edges = R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s, root = grape \<rparr>"

definition V\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e :: "wine concept set"
  where "V\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e = {estate, colour}"

definition R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e :: "wine edge set"
  where "R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e = {(estate, colour)}"

definition G\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e :: "wine rgraph"
  where "G\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e = \<lparr>vertices = V\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e, edges = R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e, root = colour \<rparr>"

definition  \<G> ::  "wine rgraph set"
  where "\<G> = {G\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s, G\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e}"

locale wine_dont = 
  dont: domain_ontology where A\<^sub>C = A\<^sub>C and A\<^sub>L = A\<^sub>L and \<G> = \<G>
  for  A\<^sub>C :: "wine concept set"
   and A\<^sub>L :: "wine concept set"
   and \<G> ::  "wine rgraph set" + 
assumes 
      atom_l_def: "A\<^sub>L = WineDOnt.A\<^sub>L"
  and atom_c_def: "A\<^sub>C = WineDOnt.A\<^sub>C"
  and graphs_def: "\<G> = WineDOnt.\<G>"
  and R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s_trans: "is_trans R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s"  
begin
print_locale! wine_dont

definition R\<^sub>p\<^sub>o\<^sub>s\<^sub>s\<^sub>i\<^sub>b\<^sub>l\<^sub>y\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e :: "wine edge set" where 
  "R\<^sub>p\<^sub>o\<^sub>s\<^sub>s\<^sub>i\<^sub>b\<^sub>l\<^sub>y\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e = R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s  O R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e"

end (* locale wine_dont *)

text \<open>Simple results: to show an element is not part of the set of concepts  \<open>A\<^sub>L\<close>, we show it is 
      distinct from all the elements in that set\<close>
context wine_dont
begin
lemma (in wine_dont) gc: "grape \<in> A\<^sub>C"
  using A\<^sub>L_def dont.atomsL_in_C atom_l_def by auto
lemma (in wine_dont) producer_in_ac: "producer \<in> A\<^sub>C"
  by (simp add: V\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s_def A\<^sub>C_def atom_c_def non_lattice_atoms_def)
lemma (in wine_dont) producer_neq_name: "producer \<noteq> grape"
  by (simp add: producer_def grape_def)
lemma (in wine_dont) producer_neq_sugar: "producer \<noteq> sugar" 
  by (simp add: producer_def sugar_def)
lemma (in wine_dont) el: "producer \<notin> A\<^sub>L"
  by (simp add: A\<^sub>L_def atom_l_def producer_def grape_def sugar_def body_def colour_def)
end

context wine_dont
begin

text \<open>Composition of \<open>grape\<close> and \<open>sugar\<close> is not an element of the set of atoms.\<close>

lemma (in wine_dont) l0: "sugar\<^sub>a\<^sub>t \<in> (grape \<oplus>\<^sub>C sugar)"
  by (simp add: oplus_def sugar_def)

lemma (in wine_dont) l1: "(grape \<oplus>\<^sub>C sugar) \<notin> A\<^sub>L"
proof - 
  have f1: "grape \<noteq> (grape \<oplus>\<^sub>C sugar)"
    by (simp add: oplus_def sugar_def grape_def) 
  have f2: "sugar \<noteq> (grape \<oplus>\<^sub>C sugar)"
    by (simp add: oplus_def sugar_def grape_def) 
  have f3: "body \<noteq> (grape \<oplus>\<^sub>C sugar)"
    using l0 body_def by blast
  then have "colour \<noteq> (grape \<oplus>\<^sub>C sugar)"
    using l0 colour_def by blast
  then show ?thesis
    using A\<^sub>L_def atom_l_def grape_def oplus_def sugar_def body_def colour_def 
          f1 f2 f3 by blast
qed

lemma (in wine_dont) l2: "(grape \<oplus>\<^sub>C sugar) \<notin> non_lattice_atoms"
proof - 
  have f: "sugar\<^sub>a\<^sub>t \<notin> producer" "sugar\<^sub>a\<^sub>t \<notin> region" "sugar\<^sub>a\<^sub>t \<notin> estate" 
    apply (simp add: producer_def)
    apply (simp add: region_def)
    apply (simp add: estate_def)
    done
  then show ?thesis 
    using l0 non_lattice_atoms_def
    by blast
qed 

text \<open>Composition of \<open>grape\<close> and \<open>sugar\<close> is an element of the monoid carrier set.\<close>
lemma (in wine_dont) l3: "(grape \<oplus>\<^sub>C sugar) \<in> dont.cmonoid.C"
  using dont.graph_carriers_in_C \<G>_def graphs_def by blast

lemma (in wine_dont) l4: "(grape \<oplus>\<^sub>C sugar) \<in> dont.clattice.L"
  by (metis A\<^sub>L_def Un_commute Un_insert_right atom_l_def dont.clattice.L_def 
      dont.clattice.oplus_closed_L insertCI insert_subset oplus_closure.a_in_A 
      subset_insertI sup_bot.left_neutral)

text \<open>There are elements in the monoid carrier set that are not elements of the atoms set. \<close>
lemma (in wine_dont) l5: "\<exists>a. a \<in> dont.cmonoid.C \<and> a \<notin> non_lattice_atoms"
  using l2 l3 by auto

text \<open>More results: concept \<open>grape\<close> and \<open>sugar\<close> are not \<open>partOf\<close> each other\<close>
lemma (in wine_dont) gr_notpart_sugar: "\<not> (grape \<sqsubseteq>\<^sub>C sugar)"
  by (simp add: grape_def partOf_def sugar_def)
lemma (in wine_dont) gr_notpart_body: "\<not> (grape \<sqsubseteq>\<^sub>C body)"
  by (simp add: grape_def partOf_def body_def)
lemma (in wine_dont) gr_notpart_colour: "\<not> (grape \<sqsubseteq>\<^sub>C colour)"
  by (simp add: grape_def partOf_def colour_def)
lemma (in wine_dont) sugar_notpart_name: "\<not> (sugar \<sqsubseteq>\<^sub>C grape)"
  by (simp add: grape_def partOf_def sugar_def)
lemma (in wine_dont) body_notpart_name: "\<not> (body \<sqsubseteq>\<^sub>C grape)"
  by (simp add: grape_def partOf_def body_def)
lemma (in wine_dont) colour_notpart_name: "\<not> (colour \<sqsubseteq>\<^sub>C grape)"
  by (simp add: grape_def partOf_def colour_def)
text \<open>Concept \<open>grape\<close> is an atom of the lattice set of atoms \<open> A\<^sub>L\<close>.\<close>

lemma (in wine_dont) "isAtom grape A\<^sub>L"
  using grape_def isAtom_def  A\<^sub>L_def 
        sugar_notpart_name body_notpart_name colour_notpart_name
  using atom_l_def empty_iff insert_iff by blast

text \<open>However, the composite concept \<open>grape \<oplus>\<^sub>C sugar\<close> is not an atom of the lattice atoms; it is 
not even a member of that set, as demonstrated in lemma b2.\<close>
lemma (in wine_dont) "\<not> (isAtom (grape \<oplus>\<^sub>C sugar) A\<^sub>L)"
  using l1 l2 isAtom_def by auto 
end

end (* Theory WineDOnt *)
