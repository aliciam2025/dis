(*  Title:     DDVTypes.thy
    Author:    Alicia Marinache
    Date:      July 25, 2023
    Modified:  June 3, 2024
*)

section \<open>Domain Data View Types\<close>

text \<open>The Domain Data View is built using a Cylindric Algebra whose carrier set elements are 
records of data. Usually, a record is represented as a tuple of values, each value corresponding to 
an attribute in the dataset. Tuples are ordered structures, and the cylindric algebra is based 
on a Boolean algebra. Thus, to achieve the commutativity of the Boolean algebra operators, 
the records must be unordered. In our interpretation, a record is a set of \<^term>\<open>sdatum\<close>. 
 \<close>

theory DDVTypes
  imports
    Main

begin

subsection \<open>Polimorphic Type: Definitions\<close>

text \<open>In Isabelle, sets are monomorphic, therefore we create a datatype \<^term>\<open>dtype\<close> to 
simulate polimorphic types. This is not a perfect solution, because datatypes are not 
extendable.\<close>
datatype dtype = Nat nat | Int int | Bool bool | Str string 

text \<open>To help construction of the generic \<^term>\<open>dtype\<close> from concrete types, we provide
translation functions.\<close>
(* They will be replaced by one generic method with a \<open>case\<close> statement. *)
definition nat2dtype :: "nat set \<Rightarrow> dtype set"
  where "nat2dtype s = {Nat n | n. n \<in> s}"

definition int2dtype :: "int set \<Rightarrow> dtype set"
  where "int2dtype s = {dtype.Int i | i. i \<in> s}"

definition bool2dtype :: "bool set \<Rightarrow> dtype set"
  where "bool2dtype s = {Bool b | b. b \<in> s}"

definition str2dtype :: "string set \<Rightarrow> dtype set"
  where "str2dtype s = {Str x | x. x \<in> s}"

type_synonym sort = "dtype set"

subsection \<open>Sorted-values, -datums, and -datas: Definitions\<close>

text \<open>The \<^term>\<open>svalue\<close> record is a pair (sort-name, sort-value).
It is the foundation of transforming a data record tuple (ordered structure) into a set of pairs 
(unordered structure). In doing so, the usual operators on sets 
(union, intersection) ensure the commutativity of operators required by the Boolean algebra.\<close>

type_synonym svalue = "string \<times> dtype"

definition make_svalue :: "string \<Rightarrow> dtype \<Rightarrow> svalue" ("\<langle>_, _\<rangle>")  where
  "\<langle>s, v\<rangle> = (s, v)" 

definition sname :: "svalue \<Rightarrow> string" where "sname x = fst x"
definition sval :: "svalue \<Rightarrow> dtype" where "sval x = snd x"

text \<open>The following type synonyms are syntactic sugar, to simplify notation and understanding of 
the Domain Data View (DDV) structures. A set of \<^term>\<open>svalue\<close>s is abbreviated as an \<^term>\<open>sdatum\<close>,
and a set of \<^term>\<open>sdatum\<close>s is abbreviated as an \<^term>\<open>sdata\<close>. The carrier set of the cylidric 
algebra consists of \<^term>\<open>sdata\<close>s.\<close>

type_synonym sdatum = "svalue set"
type_synonym sdata = "sdatum set"

definition is_sdwf :: "sdatum \<Rightarrow> bool" 
  where "is_sdwf dt \<equiv> True"

subsection \<open>Sorted-values: Properties\<close>
lemma svalue_eq [iff]: "x = y \<longleftrightarrow> (sname x = sname y \<and> sval x = sval y)"
  by (metis prod_eqI sname_def sval_def)

lemma svalue_neq_fst: "sname x \<noteq> sname y \<Longrightarrow> x \<noteq> y"
  by auto
lemma svalue_neq_snd: "sval x \<noteq> sval y \<Longrightarrow> x \<noteq> y"
  by auto

(*
text \<open>Similar to the other translation functions, we provide a generic constructor for an 
 \<^term>\<open>svalue\<close>.\<close>

definition make_nat_sdatum :: "string \<Rightarrow> nat \<Rightarrow> svalue" ("\<langle>_, _\<rangle>\<^sub>n")  where
  "\<langle>s, v\<rangle>\<^sub>n = \<lparr>sname=s, sval = Nat v\<rparr>"
definition make_bool_sdatum :: "string \<Rightarrow> bool \<Rightarrow> svalue" ("\<langle>_, _\<rangle>\<^sub>b") where
  "\<langle>s, v\<rangle>\<^sub>b = \<lparr>sname=s, sval = Bool v\<rparr>"
*)

end (* theory DDVTypes *)
