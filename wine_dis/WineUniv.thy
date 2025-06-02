(*  Title:      WineUniv.thy
    Author:     Alicia Marinache
    Date:       September 27, 2023
    Updated:    June 02, 2025
*)

section \<open>Wine Universe\<close>
text \<open>A model of the Universe theory,the  Wine Universe is implemented as an instantiation of 
      the \<open>universe\<close> locale. Foundational elements, such as the sorts and their mappings 
      are defined in this section.\<close>

theory WineUniv
  imports "../DIS/DDVUniverse"

begin

text \<open>The sorts of the universe, given as finite sets. They can be imported using the templates.\<close>
definition S\<^sub>W :: sort where 
  "S\<^sub>W = {Str ''Merlot'', Str ''Chardonay'', Str ''Vidal Blanc'', Str ''Magliocco''}"

definition S\<^sub>C :: sort where 
  "S\<^sub>C = {Str ''Red'', Str ''White'', Str ''Rose''}"

definition S\<^sub>S :: sort where 
  "S\<^sub>S = {Str ''Dry'', Str ''Sweet''}"

definition S\<^sub>B :: sort where 
  "S\<^sub>B = {Str ''Full'', Str ''Medium'', Str ''Fruity''}"

definition \<U> :: "sort set" where 
  "\<U> = {S\<^sub>W, S\<^sub>C, S\<^sub>S, S\<^sub>B}"

text \<open>The mappings (helper operators), bijections between sorts and their names.\<close>
definition wine_sort_to_name :: "sort \<Rightarrow> string" ("s2n _" [99] 100)  where
  "(s2n s)  = (if s = S\<^sub>W then ''wine'' else 
               (if s = S\<^sub>C then ''col'' else
                (if s = S\<^sub>S then ''sugar'' else 
                 (if s = S\<^sub>B then ''body'' else undefined))))"

definition wine_name_to_sort :: "string \<Rightarrow> sort" ("n2s _" [99] 100)  where
  "(n2s n)  = (if n = ''wine'' then S\<^sub>W else 
               (if n = ''col'' then S\<^sub>C else 
                (if n = ''sugar'' then S\<^sub>S else 
                 (if n = ''body'' then S\<^sub>B else undefined))))"

text \<open>The instantiation of the \<^term>\<open>universe\<close> locale with the given universe and its mappings\<close>
locale wine_univ = 
  wine_univ: universe where \<U> = \<U>  and sort2name = sort2name and name2sort = name2sort
  for  \<U> :: "sort set"
   and sort2name :: "sort \<Rightarrow> string"
   and name2sort :: "string \<Rightarrow> sort" + 
 assumes univ_def: "\<U> = WineUniv.\<U>"
     and s2n_def: "sort2name s = s2n s"
     and n2s_def: "name2sort n = n2s n"
begin
end

context wine_univ
begin
text \<open>Optional, a list of svalues that will be used later in reasoning. 
      Syntactic sugar, for ease of use only.\<close>

  definition merlot :: svalue where "merlot = \<llangle>S\<^sub>W, Str ''Merlot''\<rrangle>"
  definition chard :: svalue where "chard = \<llangle>S\<^sub>W, Str ''Chardonay''\<rrangle>"
  definition vidal :: svalue where "vidal = \<llangle>S\<^sub>W, Str ''Vidal Blanc''\<rrangle>"
  definition magliocco :: svalue where "magliocco = \<llangle>S\<^sub>W, Str ''Magliocco''\<rrangle>"

  definition red :: svalue where "red = \<llangle>S\<^sub>C, Str ''Red''\<rrangle>"
  definition white :: svalue where "white = \<llangle>S\<^sub>C, Str ''White''\<rrangle>"
  definition rose :: svalue where "rose = \<llangle>S\<^sub>C, Str ''Rose''\<rrangle>"
  
  definition dry :: svalue where "dry = \<llangle>S\<^sub>S, Str ''Dry''\<rrangle>"
  definition sweet :: svalue where "sweet = \<llangle>S\<^sub>S, Str ''Sweet''\<rrangle>"
  
  definition medium :: svalue where "medium = \<llangle>S\<^sub>B, Str ''Medium''\<rrangle>"
  definition full :: svalue where "full = \<llangle>S\<^sub>B, Str ''Full''\<rrangle>"
  definition fruity :: svalue where "fruity = \<llangle>S\<^sub>B, Str ''Fruity''\<rrangle>"
end

end