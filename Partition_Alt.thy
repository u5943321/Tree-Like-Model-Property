(* Title:        Part of the Modal Model Theory project
 * Author:       Yiming Xu, 2024
 * Content:      An alternative definition of partition,
                 so the relation does not have to be changed when taking
                 the quotient of different sets.
 *)


theory "Partition_Alt"
  imports Main
begin

definition refl' :: " 'a set => ('a \<times> 'a) set \<Rightarrow> bool" where
"refl' A r \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (a,a) \<in> r)"


definition equiv' :: "'a set => ('a \<times> 'a) set =>  bool" where
"equiv' A r \<equiv> refl' A r \<and> sym_on A r \<and> trans_on A r"

definition rclass :: " 'a set \<Rightarrow>('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set"  
  where "rclass A r a = {a'. a'\<in>A \<and> (a, a') \<in> r}"

definition quotient' :: "'a set \<Rightarrow>('a \<times> 'a) set => 'a set set"
  where
"quotient' A r = {rclass A r a | a. a \<in> A}"

lemma equiv'_subset:
  assumes "equiv' A r"
     and "B \<subseteq> A"
   shows "equiv' B r"
  using assms unfolding equiv'_def refl'_def sym_on_def trans_on_def
  by blast

lemma equiv'_inter_refl_on: 
  assumes "equiv' A r"
  shows "refl_on A (r \<inter> A\<times> A)"
  using assms unfolding equiv'_def refl_on_def refl'_def 
  by blast

lemma equiv'_inter_sym: 
  assumes "equiv' A r"
  shows "sym (r \<inter> A\<times> A)"
  using assms unfolding equiv'_def refl_on_def refl'_def sym_on_def
  sym_def 
  by blast

lemma equiv'_inter_trans: 
  assumes "equiv' A r"
  shows "trans (r \<inter> A\<times> A)"
  using assms unfolding equiv'_def refl_on_def refl'_def trans_on_def
  trans_def 
  by blast

lemma equiv'_equiv:
  assumes "equiv' A r"
  shows "equiv A (r \<inter> A\<times> A)"
  unfolding equiv_def
  using equiv'_inter_refl_on equiv'_inter_sym equiv'_inter_trans assms
  by blast


lemma rclass_Image:
  assumes "equiv' A r"
  and "a \<in> A"
shows "rclass A r a = (r \<inter> A\<times> A) `` {a}"
  using assms unfolding Image_def rclass_def 
  by blast

lemma quotient'_quotient:
  assumes "equiv' A r"
  shows
  "quotient' A r = A // (r \<inter> A\<times> A)"
  using assms  rclass_Image unfolding quotient_def quotient'_def
  by fastforce


lemma rclass_subseteq:
  "rclass A r a \<subseteq> A"
  unfolding rclass_def
  by auto

lemma rclass_monotone:
  assumes "A \<subseteq> B"
  shows "rclass A r a \<subseteq> rclass B r a"
  unfolding rclass_def
  using assms by blast


lemma rclass_subseteq_rclass:
  assumes "rclass A r a \<subseteq> B"
  shows "rclass A r a \<subseteq> rclass B r a"
  using assms unfolding rclass_def 
  by blast

lemma in_quotient_subseteq_rclass:
  assumes eqr: "equiv' A r"
  and B: "B\<subseteq> A"
  and r: "\<And> a b.  (a,b) \<in> r \<Longrightarrow> a \<in> B \<Longrightarrow> b \<in> B"
  and b0: "b0 \<in> B"
shows "rclass A r b0 = rclass B r b0" unfolding Set.set_eq_subset
proof (intro conjI)
  have "rclass A r b0 \<subseteq> B" unfolding rclass_def using r b0 by blast
  then show "rclass A r b0 \<subseteq> rclass B r b0" 
    using rclass_subseteq_rclass  by metis
  show "rclass B r b0 \<subseteq> rclass A r b0" using B rclass_monotone by metis
qed    

lemma in_quotient_union:
  assumes eqr:"equiv' (A \<union> B) r"
  and rd: "\<And>a b. a \<in> A \<Longrightarrow>  b \<in> B \<Longrightarrow> (a,b) \<notin> r"
  and inu: "x \<in> quotient' (A \<union> B) r"
  and notinb:"x \<notin> quotient' B r" 
  shows ina: "x \<in> quotient' A r" using assms
proof -  
  from inu 
  obtain x0 where xab:"x0 \<in> A \<union> B" and xrc:"x = rclass (A \<union> B) r x0"
    using quotient'_def
    by (smt (verit, best) mem_Collect_eq)
  consider (c1) "x0 \<in> A" | (c2) "x0 \<in> B" using xab by blast
  then show ?thesis
  proof (cases)
    case c1
    then have "rclass (A \<union> B) r x0 = rclass A r x0" 
      using in_quotient_subseteq_rclass rd 
      by (smt (verit) CollectD Un_iff rclass_def rclass_subseteq_rclass subset_antisym subset_eq)
    (*slow *)
    then show ?thesis using xrc unfolding quotient_def 
      using c1 quotient'_def by fastforce
  next
    case c2
    then have "False" using notinb rd
      by (smt (z3) Collect_cong UnCI UnE \<open>x = rclass (A \<union> B) r x0\<close>
 eqr equiv'_def mem_Collect_eq quotient'_def rclass_def sym_on_def)
    then show ?thesis by blast
  qed
qed


lemma equiv_on_disjoint_partition:
  assumes e:"equiv' (A \<union> B) r"
  and rd:"\<And>a b. a \<in> A \<Longrightarrow>  b \<in> B \<Longrightarrow> (a,b) \<notin> r"
  shows "quotient' (A \<union> B) r = quotient' A r \<union> quotient' B r"
proof (safe)
  show 
  "\<And>x. x \<in> quotient' (A \<union> B) r \<Longrightarrow> 
   x \<notin> quotient' B r \<Longrightarrow> x \<in> quotient' A r"
    using in_quotient_union
    using assms(1) assms(2) by blast
  have "\<And>x a. a \<in> A \<Longrightarrow> x = rclass A r a \<Longrightarrow> x = rclass (A \<union> B) r a"
  proof -
    fix x a assume "x = rclass A r a" and a:"a \<in> A"
   
    then have "rclass (A \<union> B) r a = rclass A r a"
      using in_quotient_subseteq_rclass[OF e, of A,OF _ _ a] rd
      by (smt (verit) Collect_cong Un_iff rclass_def)
    then show "\<And>x a. a \<in> A \<Longrightarrow> x = rclass A r a \<Longrightarrow> x = rclass (A \<union> B) r a"
      by (smt (verit, del_insts) Collect_cong Un_iff rclass_def rd)
  qed
  then show "\<And>x. x \<in> quotient' A r \<Longrightarrow> x \<in> quotient' (A \<union> B) r"
    by (smt (verit, del_insts) UnCI mem_Collect_eq quotient'_def)
next
  have rd' : "\<And>b a. b \<in> B \<Longrightarrow>  a \<in> A \<Longrightarrow> (b,a) \<notin> r"
    using rd e 
    by (meson equiv'_def in_mono sup_ge1 sup_ge2 sym_onD)
   have "\<And>x b. b \<in> B \<Longrightarrow> x = rclass B r b \<Longrightarrow> x = rclass (A \<union> B) r b"
  proof -
    fix x b assume "x = rclass B r b" and b:"b \<in> B"
   
    then have "rclass (A \<union> B) r b = rclass B r b"
      using in_quotient_subseteq_rclass[OF e, of B,OF _ _ b] rd'
      by (smt (verit) Collect_cong Un_iff rclass_def)
    then show "\<And>x b. b \<in> B \<Longrightarrow> x = rclass B r b \<Longrightarrow> x = rclass (A \<union> B) r b"
      by (smt (verit, del_insts) Collect_cong Un_iff rclass_def rd')
  qed
  then show "\<And>x. x \<in> quotient' B r \<Longrightarrow> x \<in> quotient' (A \<union> B) r"
    by (smt (verit, del_insts) UnCI mem_Collect_eq quotient'_def)
qed


lemma finite_finite_quotient':
  assumes "finite s"
  shows "finite (quotient' s r)"
  unfolding quotient'_def rclass_def using assms 
  by simp

lemma rclass_non_empty:
  assumes e:"equiv' A r"
  and "a \<in> A"
shows "a \<in> rclass A r a" unfolding rclass_def equiv'_def refl'_def
  using assms(2) e equiv'_def refl'_def by fastforce

lemma quotient'_class_non_empty:
  assumes "equiv' A r"
 and "c \<in> quotient' A r"
shows "c \<noteq> {}" using assms unfolding quotient'_def rclass_non_empty
  using assms(2) equiv'_equiv in_quotient_imp_non_empty 
  quotient'_quotient by blast

lemma quotient'_selection_EXISTS:
  assumes e:"equiv' A r"
  shows "\<exists>f. \<forall>c. c \<in> quotient' A r \<longrightarrow> f c \<in> c"
proof - 
  {fix c assume "c \<in> quotient' A r" 
    then have "\<exists>a. a \<in> c" using quotient'_class_non_empty 
      e by blast }
  then show ?thesis using choice 
    by meson
qed


lemma in_rclass_equiv':
  assumes "equiv' A r"
  and "a \<in> A"
  and "a' \<in> rclass A r a"
shows "(a',a) \<in> r" unfolding equiv'_def sym_on_def rclass_def
  by (metis (no_types, lifting) CollectD assms(1) assms(2) assms(3)
   equiv'_def rclass_def sym_on_def)

end