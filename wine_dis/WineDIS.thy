(*  Title:      WineDIS.thy
    Author:     Alicia Marinache
    Created:    August 8, 2023
    Updated:    June 02, 2025
*)

section \<open>Wine Domain Information System\<close>

text \<open>The Wine DIS is where everything comes together, linking the Wine DDV to the Wine DOnt.\<close>

theory WineDIS
  imports
    "../DIS/DomainInfSys"
    WineDDV
    WineDOnt
    "HOL-Eisbach.Eisbach"

begin

locale wine_dis = wine_ddv + wine_dont + 
  fixes sort2atom :: "sort \<Rightarrow> wine"
  assumes s2a_def: "sort2atom s = (if s = S\<^sub>W then grape\<^sub>a\<^sub>t else 
                                   (if s = S\<^sub>C then colour\<^sub>a\<^sub>t else 
                                    (if s = S\<^sub>B then body\<^sub>a\<^sub>t else 
                                     (if s = S\<^sub>S then sugar\<^sub>a\<^sub>t else undefined))))"
    and s2a_inj: "sort2atom x = sort2atom y \<Longrightarrow> x = y"
begin

(*
print_locale! wine_dis

lemma "x \<in> \<U> \<Longrightarrow> y \<in> \<U> \<Longrightarrow> sort2atom x = sort2atom y \<Longrightarrow> x = y"
  using s2a_def \<U>_def wine.distinct univ_def
  by (metis s2a_inj)

*)

interpretation dis A\<^sub>C A\<^sub>L \<G> \<U> sort2name name2sort D sort2atom
  apply unfold_locales
  apply (simp add: s2a_inj) 
  done

text \<open>The  wine mapping operator is defined by overwriting the DIS  mapping operator.\<close>
definition wine_type :: "sdata \<Rightarrow> wine set" ("\<tau>\<^sub>w _" [99] 100) where
  "\<tau>\<^sub>w a = \<tau> a"

text \<open>Definitions for .\<close>
definition (in wine_dis) filter0 :: "svalue \<Rightarrow> sdatum set \<Rightarrow> sdata" where 
  "filter0 sv X = Set.filter (\<lambda>x. sv \<in> x) X"

definition (in wine_dis) reds :: "sdata" where "reds = filter0 red D"
definition (in wine_dis) whites :: sdata where "whites = filter0 white D"

definition (in wine_dis) red_grapes :: "sdatum" where 
  "red_grapes = Set.filter(\<lambda>w. sname w = sort2name S\<^sub>W) (\<Union>{x. x \<in> reds})"
definition (in wine_dis) white_grapes :: "sdatum" where 
  "white_grapes = Set.filter(\<lambda>w. sname w = sort2name S\<^sub>W) (\<Union>{x. x \<in> whites})"

definition (in wine_dis)  whiteWine :: "sdatum set \<Rightarrow> dataconcept" where 
  "whiteWine X = {{dt} | dt. dt \<in> X \<and> \<tau>\<^sub>w {dt} = wine}"

end

subsection \<open>Elements of Reasoning: Consistency Checking\<close>
context wine_dis
begin
text \<open>Attribute consistency: same wine cannot be different colors in the generator set\<close>
lemma (in wine_dis) reds_whites_int: "reds \<inter> whites = {}"
  using D_def wine_generator_def reds_def whites_def WineDDV.wine_ddv.axioms
  using local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast

end

subsection \<open>Elements of Reasoning: Classification and Subsumption\<close>
context wine_dis
begin
text \<open>Classification: The merlot wine is classifed as a red wine.\<close>
lemma (in wine_dis) merlot_in_reds: "{merlot, red, dry, full} \<in> reds"
  using D_def wine_generator_def reds_def
  using wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by fastforce

text \<open>Classification: The merlot is classifed as a red grape.\<close>
lemma (in wine_dis) merlot_red: "merlot \<in> red_grapes"
  using merlot_def red_grapes_def D_def reds_def wine_generator_def wine_univ.sort_svalue
  using local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast

text \<open>Classification: The magliocco is classifed as a red grape.\<close>
lemma (in wine_dis) magliocco_red: "magliocco \<in> red_grapes"
  using magliocco_def red_grapes_def D_def reds_def wine_generator_def wine_univ.sort_svalue
  using local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast

text \<open>Other classification and subsumption results\<close>
lemma (in wine_dis) rg_def: "red_grapes = {merlot, magliocco}"
proof
  show "red_grapes \<subseteq> {merlot, magliocco}"
    using wine_ddv.a_in_one wine_ddv.dt_not_empty wine_ddv.one_closed
          local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast
next
  show "{merlot, magliocco} \<subseteq> red_grapes"
    using merlot_red magliocco_red by auto
qed

lemma (in wine_dis) wg_def: "white_grapes = {chard}"
  using ddv_base.dt_in_SD wine_ddv.ddv_base_axioms wine_ddv.dt_not_empty 
        wine_ddv.one_closed wine_ddv.one_def by blast

lemma (in wine_dis) chard_not_merlot: "chard \<noteq> merlot"
  using chard_def merlot_def svalue_eq
  using local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast

lemma (in wine_dis) chard_not_magliocco: "chard \<noteq> magliocco"
  using chard_def magliocco_def svalue_eq
  using local.univ_def wine_ddv.dt_in_SD wine_ddv.dt_v_in_k by blast

lemma (in wine_dis) chard_nred: "chard \<notin> red_grapes"
  using chard_not_magliocco chard_not_merlot rg_def by auto

lemma (in wine_dis) chard_red: "chard \<in> white_grapes"
  using chard_not_magliocco chard_not_merlot wg_def by auto

lemma (in wine_dis) "red_grapes \<inter> white_grapes = {}"
  using rg_def wg_def chard_not_merlot chard_not_magliocco by auto

end

subsection \<open>Elements of Reasoning: Concept Satisfiability\<close>
context wine_dis
begin
text \<open>Datascape concept satisfiability: The red wines \<open>reds\<close> 
      contains at lest one s-data instance.\<close>
lemma (in wine_dis) reds_satisfiable: "reds \<noteq> {}"
  using merlot_in_reds by auto

end

subsection \<open>Elements of Reasoning: Inference\<close>
context wine_dis
begin
text \<open>Inference: Region relates to  Producer, 
      Estate relate to  Grape (through \<open>(R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s)\<close>), 
      \<open>(R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s)\<close> is transitive, 
      thus Region relates to Grape.\<close>
lemma (in wine_dis) region_grape_relation: "(region, grape) \<in> R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s"
  using R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s_def R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s_trans is_trans_def
  by (metis insertCI r_r_into_trancl)

text \<open>Inference: Region relates to Estate (through \<open>(R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s)\<close>), 
                 Estate relates to Colour (through \<open>(R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e)\<close>, 
                 thus Region relates to Colour.\<close>

lemma (in wine_dis) producer_colour_relation: "(region, colour) \<in> R\<^sub>p\<^sub>o\<^sub>s\<^sub>s\<^sub>i\<^sub>b\<^sub>l\<^sub>y\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e"
  using R\<^sub>c\<^sub>o\<^sub>n\<^sub>t\<^sub>a\<^sub>i\<^sub>n\<^sub>s_def R\<^sub>p\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e_def  R\<^sub>p\<^sub>o\<^sub>s\<^sub>s\<^sub>i\<^sub>b\<^sub>l\<^sub>y\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>e_def relcomp_def
  by (metis insertCI relcomp.simps)
end

end