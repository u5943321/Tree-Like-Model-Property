(* Title:        Part of the Modal Model Theory project
 * Content:      results about generated substructs, includes from Blackburn et al.
                   - 2.6 about the preservation of satisfaction under generated substructs

 * Comment:      arguments mostly not from Blackburn et al. (left as exercises)
 *)


theory Generated_Submodel
  imports Main Modal_Syntax Modal_Model Modal_Semantics Bounded_Morphism
begin

inductive_set generated_set :: "'m set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for Op :: "'m set" and R :: "'m \<Rightarrow> 'a list \<Rightarrow> bool" and X :: "'a set"
  where
   "x \<in> X \<Longrightarrow> x \<in> generated_set Op R X"
 | "w \<in> generated_set Op R X \<Longrightarrow> m \<in> Op \<Longrightarrow> 
    R m (w # ul) \<Longrightarrow> u \<in> list.set ul \<Longrightarrow> u \<in> generated_set Op R X"


lemma generated_set_subset_world : 
  assumes M: "is_struct sig M" and X : "X \<subseteq> world M"
  shows "x \<in> generated_set Op (rel M) X \<Longrightarrow> x \<in> world M"
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case using X by blast
next
  case (2 w m ul u)
  then show ?case using M 
    by (simp add: is_struct_def) 
qed



lemma generated_set_subset_world1: 
  assumes M: "\<And>m wl. m\<in> Op\<Longrightarrow> R m wl \<Longrightarrow> set wl \<subseteq> W" and X : "X \<subseteq> W"
  shows "x \<in> generated_set Op R X \<Longrightarrow> x \<in> W"
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case using X by blast
next
  case (2 w m ul u)
  then show ?case using M 
    by fastforce
qed

definition gen_birel :: "'m set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> ('a \<times>  'a) set" 
  where 
"gen_birel Op R = {(w,u). \<exists>m ul. m \<in> Op \<and> R m (w # ul) \<and> u \<in> list.set ul}"


lemma generated_set_contns_generators:
 "X \<subseteq> generated_set ms (rel M) X" 
  by (simp add: generated_set.intros(1) subsetI)


definition is_gen_substruct::
"('m,'p) sig => ('m,'p,'a) struct \<Rightarrow> 'a set \<Rightarrow> ('m,'p,'a) struct\<Rightarrow> bool"
where 
"is_gen_substruct sig M X M1 \<equiv>
 world M1 = generated_set (ops sig) (rel M) X \<and>
 rel M1 = restrict_rel (rel M) (generated_set (ops sig) (rel M) X) \<and>
 valt M1 = restrict_valt (valt M) (generated_set (ops sig) (rel M) X)"

lemma is_gen_substruct_exists:
 "\<exists>M1. is_gen_substruct sig M X M1"
proof -
  have 
  "is_gen_substruct sig M X
   (generated_set (ops sig) (rel M) X,
    restrict_rel (rel M) (generated_set (ops sig) (rel M) X),
    restrict_valt (valt M) (generated_set (ops sig) (rel M) X))"
    unfolding is_gen_substruct_def by simp
  then show ?thesis by metis
qed

lemma gen_substruct_is_struct: 
  assumes M:"is_struct sig M" 
  and X: "X \<subseteq> world M" and "X \<noteq> {}"
  shows "is_struct sig (generated_set (ops sig) (rel M) X,
        restrict_rel (rel M) (generated_set (ops sig) (rel M) X), 
        restrict_valt (valt M) (generated_set (ops sig) (rel M) X))"
  unfolding is_struct_def fst_conv snd_conv (* apply auto *)
proof (intro conjI allI impI)
  show " generated_set (ops sig) (rel M) X \<noteq> {}" 
    by (metis assms(3) bot.extremum_uniqueI generated_set_contns_generators)
  show "\<And>m wl. 
  restrict_rel (rel M) (generated_set (ops sig) (rel M) X) m wl 
  \<Longrightarrow> m \<in> ops sig" unfolding restrict_rel_def using M 
    by (metis is_struct_def)
  show "\<And>m wl.
       restrict_rel (rel M) (generated_set (ops sig) (rel M) X)
        m wl \<Longrightarrow>
       length wl = arity sig m + 1"
   unfolding restrict_rel_def using M is_struct_def 
   by (metis Suc_eq_plus1)
  show " \<And>m wl w. restrict_rel (rel M) (generated_set (ops sig) (rel M) X) m wl \<Longrightarrow>
    w \<in> list.set wl \<Longrightarrow> w \<in> generated_set (ops sig) (rel M) X"
   unfolding restrict_rel_def
   by blast
  show "\<And>p w. restrict_valt (valt M) (generated_set (ops sig) (rel M) X) p w
      \<Longrightarrow> p \<in> props sig" unfolding restrict_valt_def using is_struct_def M
    by metis
  show "\<And>p w. restrict_valt (valt M) (generated_set (ops sig) (rel M) X) p w 
   \<Longrightarrow> w \<in> generated_set (ops sig) (rel M) X" unfolding restrict_valt_def
    by metis
qed

lemma is_gen_substruct_is_struct:
  assumes M:"is_struct sig M" 
  and X: "X \<subseteq> world M" and "X \<noteq> {}"
  and M1: "is_gen_substruct sig M X M1"
shows "is_struct sig M1" using gen_substruct_is_struct is_gen_substruct_def
  by (smt (verit, best) M M1 X assms(3) prod.collapse)



lemma gen_substruct_modal_eq : 
  assumes M:"is_struct sig M" 
  and w:"w \<in> generated_set (ops sig) (rel M) X" and phi: "wff sig phi"
  and Xss: "X \<subseteq> world M"  and Xne: "X \<noteq> {}"
shows "csatis sig M w phi \<longleftrightarrow> 
       csatis sig 
       (generated_set (ops sig) (rel M) X,
        restrict_rel (rel M) (generated_set (ops sig) (rel M) X), 
        restrict_valt (valt M) (generated_set (ops sig) (rel M) X)) w phi"
      (is "?L \<longleftrightarrow> csatis sig (?W',?R',?V') w phi")
  using phi w
proof (induction arbitrary : w rule: wff.induct)
  case cFALSE
  then show ?case by simp
next
  case (cVAR p)
  then show ?case
  unfolding 
  restrict_valt_def csatis.simps fst_conv snd_conv
     using M is_struct_def Xss
     by metis
next
  case (cDISJ f1 f2)
  then show ?case by auto
next
  case (cNOT f)
  then show ?case  using assms(4) csatis.simps(4) M generated_set_subset_world fst_eqD
    by metis
next
  case (cDIAM m fl)
  have "is_struct sig (?W',?R',?V')" using gen_substruct_is_struct[OF M Xss Xne].
  from cDIAM show ?case 
  proof (intro iffI) 
    assume LHS: "csatis sig M w (cDIAM m fl)"
    and w:"w \<in> generated_set (ops sig) (rel M) X"
    from LHS have m:"m \<in> ops sig" unfolding csatis_simps 
      using cDIAM.hyps(1) by fastforce
    from LHS have ma: "arity sig m = length fl" unfolding csatis_simps
      using cDIAM.hyps(2) by presburger
    from LHS obtain vl
    where lvlfl: "length vl = length fl"
    and rwvl:"rel M m (w # vl)"
    and ivlfl: "\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i)" 
      using csatis_simps(5) M
      by metis
    have vlgs: "\<forall>v. v \<in> list.set vl \<longrightarrow> v \<in> generated_set (ops sig) (rel M) X"  
    using w rwvl m generated_set.intros(2) 
      by metis
    then have rrwvl: "restrict_rel (rel M) (generated_set (ops sig) (rel M) X) m (w # vl)"
      unfolding restrict_rel_def w 
      by (simp add: rwvl w)
    have "\<forall>i<length vl.
              csatis sig
               (?W',?R',?V')
               (vl ! i) (fl ! i)" 
      using ivlfl vlgs lvlfl cDIAM.IH cDIAM.prems by fastforce
    then show "csatis sig (?W',?R',?V') w (cDIAM m fl)" unfolding csatis_simps
      using rrwvl cDIAM.prems(1) lvlfl m ma 
      by (metis (no_types, lifting) \<open>is_struct sig (generated_set (ops sig) (rel M) X, 
   restrict_rel (rel M) (generated_set (ops sig) (rel M) X), 
    restrict_valt (valt M) (generated_set (ops sig) (rel M) X))\<close> csatis_simps5 fst_conv snd_conv)
  next 
    assume RHS: "csatis sig (?W',?R',?V') w (cDIAM m fl)"
    and w: " w \<in> generated_set (ops sig) (rel M) X "
    from w have "w \<in> world M" using M generated_set_subset_world 
      by (metis Xss)
    then show "csatis sig M w (cDIAM m fl)" 
      using restrict_rel_def cDIAM Xss generated_set_subset_world M 
      by (smt (verit) RHS \<open>is_struct sig (generated_set (ops sig) (rel M) X, 
    restrict_rel (rel M) (generated_set (ops sig) (rel M) X), restrict_valt (valt M) 
   (generated_set (ops sig) (rel M) X))\<close> csatis_simps5 fst_conv generated_set.intros(2)
    nth_mem snd_conv)
       qed  
qed

lemmas Blackburn_prop_2_6 = gen_substruct_modal_eq 


lemma generated_set_closed:
  assumes "x \<in> generated_set sig R X"
  shows 
  "x \<in>
  generated_set sig (restrict_rel R (generated_set sig R X)) X"
  using assms
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case
    by (meson generated_set.intros(1))
next
  case (2 w m ul u)
  then
  have "\<And>u. u \<in> set ul \<Longrightarrow> u \<in> (generated_set sig R X)"
    by (meson generated_set.intros(2))
  with \<open>w \<in> generated_set sig R X\<close> \<open>R m (w # ul)\<close>
       restrict_rel_def
  have rRwul:
   "restrict_rel R (generated_set sig R X) m (w # ul)"
   by (metis (full_types) set_ConsD)
  show ?case
    using 
  generated_set.intros(2)
  [of w sig
   "restrict_rel R (generated_set sig R X)" "X" m ul u,
   OF 2(5) 2(2) rRwul 2(4)].
qed

lemma generated_set_subseteq_monotone:
  assumes "\<And>m wl. R1 m wl \<Longrightarrow> R2 m wl"
  shows "generated_set sig R1 X \<subseteq> generated_set sig R2 X"
proof (rule subsetI)
  fix x
  assume xR1:" x \<in> generated_set sig R1 X"
  then show "x \<in> generated_set sig R2 X"
  proof (induction rule: generated_set.induct)
    case (1 x)
    then show ?case
      by (simp add: generated_set.intros(1)) 
  next
    case (2 w m ul u)
    then show ?case 
      by (meson assms generated_set.intros(2))
  qed
qed

lemma generated_set_restrict_rel:
" generated_set sig R X =
  generated_set sig (restrict_rel R (generated_set sig R X)) X"
  using generated_set_closed generated_set_subseteq_monotone
         restrict_rel_def 
  by (metis (no_types, lifting) order_antisym subsetI)

lemma gen_substruct_world:
"is_gen_substruct sig aM X M \<Longrightarrow> 
world M = generated_set (ops sig) (rel M) X"
  unfolding is_gen_substruct_def
 using generated_set_restrict_rel
  by metis

lemma gen_substruct_rel_lemma:
  assumes M:"is_gen_substruct sig aM X M"
 shows "restrict_rel (rel aM)
     (generated_set (ops sig) (rel aM) X) m wl =
    restrict_rel (rel M)
     (generated_set (ops sig) (rel M) X) m wl"
proof - 
  have wM: "world M = generated_set (ops sig) (rel M) X"
    using gen_substruct_world [OF M].
  then have wM': "(generated_set (ops sig) (rel aM) X) = 
    generated_set (ops sig) (rel M) X"
    using assms is_gen_substruct_def by blast
  have "rel M = 
    restrict_rel (rel aM) 
    (generated_set (ops sig) (rel aM) X)"
    using M[unfolded is_gen_substruct_def]
    by blast
  then have 
  "restrict_rel (rel aM)
     (generated_set (ops sig) (rel M) X) m wl =
    restrict_rel (rel M)
     (generated_set (ops sig) (rel M) X) m wl"
    unfolding restrict_rel_def 
    by (metis (mono_tags) wM')
  then show ?thesis
    using wM' by auto
qed

lemma gen_substruct_rel:
  assumes M:"is_gen_substruct sig aM X M"
 shows "rel M =
    restrict_rel (rel M)
     (generated_set (ops sig) (rel M) X)"
  using  gen_substruct_rel_lemma 
proof -
  have "\<forall>a cs. rel M a cs = restrict_rel (rel M) (generated_set (ops sig) (rel M) X) a cs"
    by (smt (z3) assms gen_substruct_rel_lemma is_gen_substruct_def)
  then show ?thesis
    by blast
qed


lemma gen_substruct_valt_lemma:
  assumes M:"is_gen_substruct sig aM X M"
 shows "restrict_valt (valt aM)
     (generated_set (ops sig) (rel aM) X) p w =
    restrict_valt (valt M)
     (generated_set (ops sig) (rel M) X) p w"
proof -
have wM: "world M = generated_set (ops sig) (rel M) X"
    using gen_substruct_world [OF M].
  then have wM': "(generated_set (ops sig) (rel aM) X) = 
    generated_set (ops sig) (rel M) X"
    using assms is_gen_substruct_def by blast
  have "valt M = 
    restrict_valt (valt aM) 
    (generated_set (ops sig) (rel aM) X)"
    using M[unfolded is_gen_substruct_def]
    by blast
  then have 
  "restrict_valt (valt aM)
     (generated_set (ops sig) (rel M) X) p w =
    restrict_valt (valt M)
     (generated_set (ops sig) (rel M) X) p w"
    unfolding restrict_valt_def
    by (metis (mono_tags) wM')
  then show ?thesis
    using wM' by auto
qed


lemma gen_substruct_valt:
  assumes M:"is_gen_substruct sig aM X M"
 shows "valt M =
    restrict_valt (valt M)
     (generated_set (ops sig) (rel M) X) "
  using  gen_substruct_valt_lemma 
proof -
  have "\<forall>a cs. valt M a cs = restrict_valt (valt M) (generated_set (ops sig) (rel M) X) a cs"
    by (smt (z3) assms gen_substruct_valt_lemma is_gen_substruct_def)
  then show ?thesis
    by blast
qed



lemma gen_substruct_itself:
  assumes "is_gen_substruct sig aM X M"
 shows "is_gen_substruct sig M X M"
  unfolding is_gen_substruct_def 
  using gen_substruct_valt gen_substruct_rel
       gen_substruct_world
  by (metis assms)



lemma is_gen_substruct_alt:
 "is_gen_substruct sig M X M1 \<Longrightarrow>
 world M1 = generated_set (ops sig) (rel M1) X \<and>
 rel M1 = restrict_rel (rel M1) (generated_set (ops sig) (rel M1) X) \<and>
 valt M1 = restrict_valt (valt M1) (generated_set (ops sig) (rel M1) X)"
  using gen_substruct_itself is_gen_substruct_def 
  by blast

end