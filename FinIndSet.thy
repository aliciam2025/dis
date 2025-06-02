(*  Title:     FinIndSet.thy
    Author:    Alicia Marinache
    Date:      July 25, 2023
    Modified:  June 3, 2024
*)

section \<open>Inductive Finite Sets\<close>

text \<open>Throughout the Universe and DDV theories, we use the fact that sorts and, 
      ultimately, both sdatas and sdatums are finite sets. 
      In this section, we give the theory of inductively defined 
      finite sets, to support Universe and DDV proofs in using the inductive rule.\<close>

theory FinIndSet
  imports
    Main

begin

inductive_set Fin where
  emptyI: "{} \<in> Fin" | 
  insertI: "A \<in> Fin \<Longrightarrow> insert a A \<in> Fin"

declare Fin.intros [intro]

lemma Fin_is_finite: "x \<in> Fin \<longleftrightarrow> finite x"
proof
  show "x \<in> Fin \<Longrightarrow> finite x"
    using Fin.inducts by auto
  then show "finite x \<Longrightarrow> x \<in> Fin"
    by (metis Fin.simps Finp_Fin_eq finite_ne_induct)
qed


end