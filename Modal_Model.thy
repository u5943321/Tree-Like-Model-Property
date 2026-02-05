(* Title:        Part of the Modal Model Theory project
 * Content:      definition of modal structs following Blackburn et al.
 * Comment:      preconditions are inconvenient, I'll try to get rid of them
 *)

theory Modal_Model
  imports Main "Modal_Syntax"
begin

type_synonym ('m,'p,'a) struct = 
"'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool)"

type_synonym ('m,'a) frame = 
"'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool)"

abbreviation fworld :: 
"('m,'a) frame \<Rightarrow> 'a set" where
"fworld F \<equiv> fst F"

abbreviation frel :: 
"('m,'a) frame \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool)" where
"frel F \<equiv> snd F"

definition is_frame :: "'m msig \<Rightarrow> ('m,'a) frame \<Rightarrow> bool"
  where 
"is_frame msig F \<equiv> 
 fworld F \<noteq> {} \<and>
 (\<forall>m wl. frel F m wl \<longrightarrow> 
  m \<in> mops msig \<and> length wl = marity msig m + 1 \<and> 
  (\<forall>w. w \<in> list.set wl \<longrightarrow> w \<in> fworld F))
 "


abbreviation world :: 
"'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool)
 \<Rightarrow> 'a set" where
"world M \<equiv> fst M"

abbreviation 
rel :: "'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool)
 \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool)" where
"rel \<tau> \<equiv> fst (snd \<tau>)"

abbreviation 
valt :: "'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool) 
\<Rightarrow> ('p \<Rightarrow> 'a \<Rightarrow> bool)" where
"valt \<tau> \<equiv> snd (snd \<tau>)"


definition is_struct :: "('m,'p) sig \<Rightarrow> ('m,'p,'b) struct \<Rightarrow> bool"
  where 
"is_struct sig M \<equiv> 
 world M \<noteq> {} \<and>
 (\<forall>m wl. rel M m wl \<longrightarrow> 
  m \<in> ops sig \<and> length wl = arity sig m + 1 \<and> 
  (\<forall>w. w \<in> list.set wl \<longrightarrow> w \<in> world M)) \<and>
 (\<forall>p w. valt M p w \<longrightarrow> p \<in> props sig \<and> w \<in> world M) "


definition restrict_rel :: 
"('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool)"
where
"restrict_rel R X m l \<equiv> R m l \<and> (\<forall>x. x \<in> list.set l \<longrightarrow> x \<in> X)"

definition restrict_valt ::
"('p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('p \<Rightarrow> 'a \<Rightarrow> bool)" where
"restrict_valt V X p x \<equiv> V p x \<and> x \<in> X"


lemma struct_valt_update:
  assumes "is_struct sig M"
      and "\<And>w p. v p w \<Longrightarrow> w \<in> world M \<and> p \<in> props sig"
    shows "is_struct sig (world M, rel M, v)" 
  unfolding is_struct_def fst_conv snd_conv 
  using assms(1) assms(2) is_struct_def by blast

lemma struct_valt_update_alt:
  assumes "is_struct sig M"
      and "\<And>w p. v p w \<Longrightarrow> w \<in> world M \<and> p \<in> props sig"
    shows "\<exists>M'. is_struct sig M' \<and> world M' = world M \<and> rel M' = rel M \<and>
                valt M' = v" 
 using struct_valt_update 
  by (metis assms(1) assms(2) fst_conv snd_conv)



lemma is_struct_rel_same_length:
  assumes "is_struct sig M" 
      and "is_struct sig M'"
      and "m \<in> ops sig"
      and "rel M m wl"
      and "rel M' m wl'"
    shows "length wl = length wl'" using assms unfolding is_struct_def 
  by presburger

end