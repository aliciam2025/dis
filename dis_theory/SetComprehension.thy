(*  Title:      SetComprehension.thy
    Author:     Alicia Marinache
    Date:       June 7, 2024
    Modified:   June 7, 2024
*)

section \<open>Set Comprehension Results\<close>

text \<open>Domain Information System proofs use well-known set comprehension laws, that are 
      not found in the core of Isabelle/HOL and are proved in this section. \<close>

theory SetComprehension
  imports
    Main
begin

lemma setcomp_union: "{x. x \<in> A \<union> B} = {x. x \<in> A} \<union> {x. x \<in> B}" by auto
lemma setcomp_int: "{x. x \<in> A \<inter> B} = {x. x \<in> A} \<inter> {x. x \<in> B}" by auto
lemma setcomp_and: "{x| x. x \<in> {y| y. y \<in> A \<and> P y} \<and> Q x} = 
       {x| x. x \<in> A \<and> P x \<and> Q x}"
  by auto
lemma setcomp_congr0: 
  "{E x | x. (\<exists>y z. x = F y z) \<and> Q x} = {E x | x y z. x = F y z \<and> Q x}" by simp
lemma setcomp_congr1:  
  assumes "\<And>x y z. E x y z = F x y z"
shows "{E x y z | x y z. P x y z} = {F x y z| x y z. P x y z}"
  using assms by auto
lemma setcomp_distr0: 
      "{x| x. (x \<in> X \<and> P x) \<or> (x \<in> X \<and> Q x)} = 
       {x| x. x \<in> X \<and> (P x \<or>  Q x)}"
  by auto
lemma setcomp_distr1: 
      "{x| x. (x \<in> X \<and> P x) \<or> (x \<in> X \<and> \<not>(P x))} = {x| x. x \<in> X}"
  by auto
lemma setcomp_distr2: 
      "{x| x. (x \<in> X \<and> P x) \<and> (x \<in> X \<and> \<not>(P x))} = {}"
  by auto

lemma set_image_union: 
  shows "{f x | x. x \<in> A \<union> B} = {f x| x. x \<in> A} \<union> {f x| x. x \<in> B}"
proof - 
  have "{f x| x. x \<in> A} = f`A"
    by (simp add: Setcompr_eq_image)
  then show ?thesis 
    using Set.image_Un by auto
qed

lemma m: "X\<noteq>{} \<Longrightarrow> Y\<noteq>{} \<Longrightarrow> {{x| x. x \<in> X} | v. v \<in> Y} = {{x| x. x \<in> X}}"
  by blast

lemma "\<Union>{A} = A"
  by simp

lemma "{E x| x. x \<in> {y}} = {E y}"
  by simp
(*
lemma "x \<noteq> y \<Longrightarrow> A\<noteq>B  \<Longrightarrow> {a \<union> {x}| a. a \<in> A} \<inter> {b \<union> {y}| b. b \<in> B} = {}"

lemma "b \<notin> A \<Longrightarrow> A \<inter> X = {} \<Longrightarrow> A \<inter> {a \<union> {b}| a \<in> X} = {}"
s
*)

end