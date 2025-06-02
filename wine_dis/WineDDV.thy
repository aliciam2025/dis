(*  Title:      WineDDV.thy
    Author:     Alicia Marinache
    Date:       July 25, 2023
    Updated:    June 02, 2025
*)

section \<open>Wine Domain Data View\<close>

text \<open>A model of the Domain Data View theory,the  WineDDV is implemented as an instantiation of 
      the \<open>domain_data_view\<close> locale.\<close>

theory WineDDV
  imports
    WineUniv
    "../DIS/DomainDtVw"

begin

text \<open>The dataset that guides the construction of the entire DIS is part of the declarations, 
      given as the definition of the generator set.\<close>

context wine_univ
begin

definition wine_generator :: "sdatum set" where
  "wine_generator = {{merlot, red, dry, full}, 
                     {chard, white, dry, medium}, 
                     {vidal, rose, sweet, fruity}, 
                     {magliocco, red, dry, full}}"
end

locale wine_ddv = wine_univ + 
  wine_ddv: domain_data_view where  D = D
  for D :: "sdatum set"  + 
 assumes D_def: "D = wine_generator"
begin
end

context wine_ddv (* tests on D *)
begin

lemma (in wine_ddv) "{merlot, red, dry, full} \<in> D" 
  using D_def wine_generator_def by simp

lemma (in wine_ddv) "{merlot, red, dry, full} \<in> Set.filter (\<lambda>x. merlot \<in> x) D"
  using D_def wine_generator_def by simp

end

end (* WineDDV Theory *)
