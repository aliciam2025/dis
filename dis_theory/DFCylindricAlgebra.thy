(*  Title:      DFCylindricAlgebra.thy
    Author:     Alicia Marinache
    Date:       September 21, 2022
    Modified:   June 11, 2024
*)

section \<open>Diagonal-free Cylindric algebra\<close>

theory DFCylindricAlgebra
  imports 
    Main
    "HOL.Boolean_Algebras"

begin
text \<open>A diagonal-free algebra is a Boolean algebra with a cylindrification operator\<close>

locale dfcyl_algebra = 
   balg: abstract_boolean_algebra "mult" "plus" "compl" "zero" "one"
   for  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>*" 70)
    and plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "\<^bold>+" 65)
    and compl :: "'a \<Rightarrow> 'a"  ("\<^bold>~_" [81] 80)
    and zero :: "'a"  ("\<^bold>\<zero>")
    and one  :: "'a"  ("\<^bold>\<one>")  + 
  fixes cyl :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" ("c\<^bsub>_\<^esub> _" [91] 90)
    and carrier :: "'a set"
  assumes 
        ck_norm: "(c\<^bsub>k\<^esub> \<^bold>\<zero>) = \<^bold>\<zero>"
    and ck_mod: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> (c\<^bsub>k\<^esub> (x \<^bold>* (c\<^bsub>k\<^esub> y))) = (c\<^bsub>k\<^esub> x) \<^bold>* (c\<^bsub>k\<^esub> y)"
    and ck_comm: "x \<in> carrier \<Longrightarrow> (c\<^bsub>k\<^esub> (c\<^bsub>l\<^esub> x)) = (c\<^bsub>l\<^esub> (c\<^bsub>k\<^esub> x))"
begin
lemma (in dfcyl_algebra) ck_zero: "x \<^bold>+ (c\<^bsub>k\<^esub> \<^bold>\<zero>) = x"
  by (simp add: ck_norm)
end

end (* Theory DFCylindricAlgebra *)

