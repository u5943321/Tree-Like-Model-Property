(* Title:        Part of the Modal Model Theory project
 * Content:      definition of the semantics of modal structs following Blackburn et al.
     There are two versions of the definition, csatis takes the signature, asatis does not.
 *)


theory Modal_Semantics
  imports Main Modal_Syntax Modal_Model
begin

lemma csatis_termination_helper: 
\<open>(ac, bc) \<in> set (zip x fl) \<Longrightarrow> size bc < Suc (size_list size fl)\<close>
proof (induction fl arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case 
    by (meson Suc_n_not_le_n in_set_zipE linorder_le_less_linear size_list_estimation')
qed

lemma wf_size_csatis: "wf {((a, b, c, d), e, f, g, h). size d < size h}"
unfolding wfp_wf_eq[symmetric]
by (rule wfp_if_convertible_to_nat[of _ \<open>\<lambda>(a, b, c, d). size d\<close>])
auto


function csatis :: "('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> 'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
'a \<Rightarrow> ('m,'p) cform \<Rightarrow> bool"
where
"csatis sig M w cFALSE \<longleftrightarrow> False"
| "csatis sig M w (cVAR p) \<longleftrightarrow> valt M p w"
| "csatis sig M w (cDISJ f1 f2) = (csatis sig M w f1 \<or> csatis sig M w f2)"
| "csatis sig M w (cNOT f) = (w \<in> world M \<and> \<not> csatis sig M w f)"
| "csatis sig M w (cDIAM m fl) =
( (\<exists>vl. length vl = length fl \<and> rel M m (w # vl) \<and>
 (\<forall>x y. (x,y) \<in> set (zip vl fl) \<longrightarrow> csatis sig M x y)))"
proof-

  show "\<And>P x. (\<And>sig M w. x = (sig, M, w, cFALSE) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>sig M w p. x = (sig, M, w, cVAR p) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>sig M w f1 f2.
               x = (sig, M, w, cDISJ f1 f2) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>sig M w f. x = (sig, M, w, cNOT f) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>sig M w m fl.
               x = (sig, M, w, \<diamondsuit>m fl) \<Longrightarrow> P) \<Longrightarrow>
           P"
    by (metis cform.exhaust prod_cases4)
  
qed auto
termination 
by (relation \<open>{((a,b,c,d),e,f,g,h). size d < size h}\<close>)
(auto simp: csatis_termination_helper wf_size_csatis)

(*csatis sig M w (cVAR p) \<longleftrightarrow> p \<in> props sig \<and> w \<in> world M \<and> valt M p w*)

lemma castis_simps1:
 assumes "is_struct sig M"
  shows "csatis sig M w (cVAR p) = (p \<in> props sig \<and> w \<in> world M \<and> valt M p w)"
proof - 
  have "\<And>p w.  valt M p w \<Longrightarrow> p \<in> props sig \<and> w \<in> world M"
    using is_struct_def assms
    by metis
  then show ?thesis unfolding csatis.simps 
    by blast
qed

lemma csatis_simps5:
  assumes "is_struct sig M"
  shows "csatis sig M w (cDIAM m fl) =
  (m \<in> ops sig \<and>
   arity sig m = length fl \<and>
   w \<in> world M \<and>
   (\<exists>vl. length vl = length fl \<and> rel M m (w # vl) \<and> 
   (\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i))))"
proof -
  have "\<And>vl fl. length vl = length fl \<Longrightarrow> 
  (\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> csatis sig M x y) \<longleftrightarrow>
  (\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i))" 
    using in_set_zip by fastforce
  have 
  a1:"\<And>m w vl. rel M m (w # vl) \<Longrightarrow> w \<in> world M \<and> set vl \<subseteq> world M"
    by (meson assms is_struct_def list.set_intros(1) set_subset_Cons subset_code(1))
  have 
  a2:"\<And>m w vl. rel M m (w # vl) \<Longrightarrow> length vl = arity sig m"
    using assms
    by (metis (no_types, lifting) One_nat_def add_right_imp_eq is_struct_def list.size(4))
  then show ?thesis unfolding csatis.simps using a1 a2 
    by (smt (verit) \<open>\<And>vl fl. length vl = length fl \<Longrightarrow> 
    (\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> csatis sig M x y) = 
  (\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i))\<close> assms is_struct_def)
   
qed

lemma csatis_simps:
  assumes "is_struct sig M"
  shows "csatis sig M w cFALSE = False" 
"csatis sig M w (cVAR p) = (p \<in> props sig \<and> w \<in> world M \<and> valt M p w)"
"csatis sig M w (cDISJ f1 f2) = (csatis sig M w f1 \<or> csatis sig M w f2)"
"csatis sig M w (cNOT f) = (w \<in> world M \<and> \<not> csatis sig M w f)"
"csatis sig M w (cDIAM m fl) =
  (m \<in> ops sig \<and>
   arity sig m = length fl \<and>
   w \<in> world M \<and>
   (\<exists>vl. length vl = length fl \<and> rel M m (w # vl) \<and> 
   (\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i))))"
proof - 
  show "csatis sig M w (cDIAM m fl) =
    (m \<in> ops sig \<and>
     arity sig m = length fl \<and>
     w \<in> world M \<and>
     (\<exists>vl. length vl = length fl \<and>
           rel M m (w # vl) \<and>
           (\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i))))"
    using assms by (meson csatis_simps5)
next
  show "csatis sig M w (cVAR p) = (p \<in> props sig \<and> w \<in> world M \<and> valt M p w)"
    using assms 
    by (metis castis_simps1)
qed simp_all


lemma csatis_in_world : 
 assumes "is_struct sig M"
 shows "csatis sig M w phi \<Longrightarrow> w \<in> world M"
proof (induction phi arbitrary: w rule: cform.induct)
  case (cVAR x)
  then show ?case
    by (meson assms castis_simps1)
next
  case cFALSE
  then show ?case 
    by (metis csatis.simps(1))
next
  case (cDISJ x1a x2)
  then show ?case
    by (metis csatis.simps(3))
next
  case (cNOT x)
  then show ?case 
    by (metis csatis.simps(4))
next
  case (cDIAM x1a x2)
  then show ?case
    by (metis assms csatis_simps5)
qed





lemma asatis_termination_helper: 
\<open>(ac, bc) \<in> set (zip x fl) \<Longrightarrow> size bc < Suc (size_list size fl)\<close>
proof (induction fl arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case 
    by (meson Suc_n_not_le_n in_set_zipE linorder_le_less_linear size_list_estimation')
qed

lemma wf_size_asatis: "wf {(( b, c, d), f, g, h). size d < size h}"
unfolding wfp_wf_eq[symmetric]
by (rule wfp_if_convertible_to_nat[of _ \<open>\<lambda>( b, c, d). size d\<close>])
auto



function asatis :: " 'a set \<times> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
'a \<Rightarrow> ('m,'p) cform \<Rightarrow> bool"
where
"asatis M w cFALSE \<longleftrightarrow> False"
| "asatis M w (cVAR p) \<longleftrightarrow> w \<in> world M \<and> valt M p w"
| "asatis M w (cDISJ f1 f2) = (asatis M w f1 \<or> asatis M w f2)"
| "asatis M w (cNOT f) = (w \<in> world M \<and> \<not> asatis M w f)"
| "asatis M w (cDIAM m fl) =
(w \<in> world M \<and> (\<exists>vl. length vl = length fl \<and> rel M m (w # vl) \<and>
(\<forall>x y. (x,y) \<in> set (zip vl fl) \<longrightarrow> asatis M x y)))"
proof-

  show " \<And>P x. (\<And>M w. x = (M, w, cFALSE) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>M w p. x = (M, w, cVAR p) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>M w f1 f2. x = (M, w, cDISJ f1 f2) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>M w f. x = (M, w, cNOT f) \<Longrightarrow> P) \<Longrightarrow> 
 (\<And>M w m fl. x = (M, w, \<diamondsuit>m fl) \<Longrightarrow> P) \<Longrightarrow> P
"
    
    by (metis cform.exhaust prod_cases3)
  
qed auto
termination 
by (relation \<open>{((b,c,d),f,g,h). size d < size h}\<close>)
(auto simp: asatis_termination_helper wf_size_asatis)

lemma asatis_empty_cDIAM:
 "asatis M w (cDIAM m []) \<equiv> w \<in> world M \<and> rel M m [w]"
  by simp

lemma cDIAM_empty_asatis_exists0:
  fixes m0
  defines "W \<equiv> {undefined}"
  defines "R \<equiv> \<lambda>m wl. m = m0 \<and> wl = [undefined]"
  shows "asatis (W,R,V) undefined  (cDIAM m0 [])"
  unfolding asatis_empty_cDIAM 
  by (simp add: R_def W_def)

lemma cDIAM_empty_asatis_exists0':
  fixes m0
  defines "W \<equiv> {undefined}"
  defines "R \<equiv> \<lambda>m wl. m = m0 \<and> wl = [undefined]"
  shows "asatis (W,R,V) undefined  (cDIAM m0 []) \<and>
  (\<forall>l. length l \<noteq> 0 \<longrightarrow> \<not>asatis (W,R,V) undefined  (cDIAM m l))"
  unfolding asatis_empty_cDIAM  R_def W_def 
  by force



lemma csatis_asatis: 
  assumes "is_struct sig M"
  shows "csatis sig M w phi = asatis M w phi" using assms
proof (induction phi arbitrary: w)
  case (cVAR x)
  then show ?case unfolding is_struct_def by auto 
next
  case cFALSE
  then show ?case by auto
next
  case (cDISJ phi1 phi2)
  then show ?case by auto
next
  case (cNOT phi)
  then show ?case by auto
next
  case (cDIAM m fl)
  show ?case 
  proof (rule iffI)
    assume "csatis sig M w (\<diamondsuit>m fl)"
    then show "asatis M w (\<diamondsuit>m fl)" 
      by (meson asatis.simps(5) assms cDIAM.IH csatis.simps(5) csatis_in_world set_zip_rightD)
  next 
    assume "asatis M w (\<diamondsuit>m fl)" 
    then show "csatis sig M w (\<diamondsuit>m fl)"
      by (meson asatis.simps(5) assms cDIAM.IH csatis.simps(5) set_zip_rightD)
  qed
qed


lemma asatis_in_world : "asatis M w phi \<Longrightarrow> w \<in> world M"
proof (induction phi arbitrary: w rule: cform.induct)
  case (cVAR x)
  then show ?case 
    by (metis asatis.simps(2))
next
  case cFALSE
  then show ?case 
    by (metis asatis.simps(1))
next
  case (cDISJ x1a x2)
  then show ?case
    by (metis asatis.simps(3))
next
  case (cNOT x)
  then show ?case 
    by (metis asatis.simps(4))
next
  case (cDIAM x1a x2)
  then show ?case using asatis.simps(5) 
    by (metis)
qed

lemma asatis_prop_letters:
  assumes V:"\<And>p w. p \<in> prop_letters phi \<Longrightarrow> valt M1 p w = valt M2 p w"
  and W:"world M1 = world M2"
  and R: "rel M1  = rel M2"
  and w : "w \<in> world M1"
  shows "asatis M1 w phi \<equiv> asatis M2 w phi" using w V
proof (induction phi arbitrary : w)
  case (cVAR x)
  then show ?case using W V by auto 
next
  case cFALSE
  then show ?case  by auto
next
  case (cDISJ phi1 phi2)
  then show ?case by auto
next
  case (cNOT phi)
  then show ?case using W by auto 
next
  case (cDIAM m fl)
  then show ?case unfolding prop_letters.simps
  proof (intro iffI)
    assume l:"asatis M1 w \<diamondsuit>m fl"
    then have "w \<in> world M1" 
      using cDIAM.hyps(2) by blast
    obtain vl where 
    "length vl = length fl" 
    and "rel M1 m (w # vl)" 
    and vlfl1:"\<And>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M1 x y"
      using l by auto
    then have 
    "\<And>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M2 x y" using cDIAM.hyps
    proof (intro impI)
      fix x y assume xy:"(x, y) \<in> set (zip vl fl)" 
      then have " asatis M1 x y" using vlfl1 by blast
      have yfl: "y \<in> set fl" using xy 
        by (metis set_zip_rightD)
       have "prop_letters y \<subseteq> \<Union> (set (map prop_letters fl))" 
      using yfl by auto
     then have "\<And>p w. p \<in> prop_letters y \<Longrightarrow> valt M1 p w = valt M2 p w"
        using cDIAM.hyps(3) yfl prop_letters.simps(5) 
        by auto
      then show "asatis M2 x y" 
        by (meson \<open>asatis M1 x y\<close> asatis_in_world cDIAM.hyps(1) yfl)
    qed
    then show "asatis M2 w \<diamondsuit>m fl" unfolding asatis.simps
      using R 
      using W \<open>length vl = length fl\<close> 
    \<open>rel M1 m (w # vl)\<close> cDIAM.hyps(2) by auto
  next 
  assume l:"asatis M2 w \<diamondsuit>m fl"
    then have "w \<in> world M2" 
      using asatis_in_world by simp
    obtain vl where 
    "length vl = length fl" 
    and "rel M2 m (w # vl)" 
    and vlfl1:"\<And>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M2 x y"
      using l by auto
    then have 
    "\<And>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M1 x y" using cDIAM.hyps
    proof (intro impI)
      fix x y assume xy:"(x, y) \<in> set (zip vl fl)" 
      then have " asatis M2 x y" using vlfl1 by blast
      have yfl: "y \<in> set fl" using xy 
        by (metis set_zip_rightD)
       have "prop_letters y \<subseteq> \<Union> (set (map prop_letters fl))" 
      using yfl by auto
      then have "\<And>p w. p \<in> prop_letters y \<Longrightarrow> valt M1 p w = valt M2 p w"
        using cDIAM.hyps(3) yfl prop_letters.simps(5) 
        by auto
      then show "asatis M1 x y" 
        by (metis W \<open>asatis M2 x y\<close> asatis_in_world cDIAM.hyps(1) yfl)
    qed
    then show "asatis M1 w \<diamondsuit>m fl" unfolding asatis.simps
      using R 
      using W \<open>length vl = length fl\<close> 
    \<open>rel M2 m (w # vl)\<close> cDIAM.hyps(2) by auto
  qed
qed

definition cequiv :: 
"('a::type) itself \<Rightarrow> ('m,'p) cform => ('m,'p) cform \<Rightarrow> bool" 
where 
"cequiv (TYPE ('a)) f1 f2 \<equiv> 
 (\<forall>M w::'a.  asatis M w f1 = asatis M w f2)"

lemma cequiv_equiv: 
"equiv UNIV {(f1,f2) . cequiv (TYPE ('a)) f1 f2}"
  unfolding cequiv_def equiv_def refl_on_def sym_on_def trans_on_def by simp 

definition cequiv_on :: 
"('a::type) itself \<Rightarrow> ('m,'p) cform set \<Rightarrow>
 (('m,'p) cform \<times> ('m,'p) cform) set" where
"cequiv_on (TYPE ('a)) S = 
 {(f1,f2). f1 \<in> S \<and> f2 \<in> S \<and> cequiv (TYPE ('a)) f1 f2}"

lemma cequiv_relation_equiv: 
"equiv C (cequiv_on TYPE('a) C)"
  unfolding cequiv_on_def cequiv_def equiv_def refl_on_def sym_on_def trans_on_def by auto 

lemma cequiv_cequiv_on:
  assumes "cequiv TYPE('a) f1 f2"
      and "f1 \<in> C" and "f2 \<in> C"
    shows "(f1,f2) \<in> cequiv_on TYPE('a) C" using assms
  unfolding cequiv_def cequiv_on_def 
  by blast

lemma cequiv_cNOT_cong: 
"cequiv TYPE('a) a b \<Longrightarrow> cequiv TYPE('a) (cNOT a) (cNOT b)"
  by (simp add: cequiv_def)

lemma cequiv_cDISJ_cong: 
"cequiv TYPE('a) a1 a2 \<Longrightarrow>cequiv TYPE('a) b1 b2 \<Longrightarrow>
 cequiv TYPE('a) (cDISJ a1 b1) (cDISJ a2 b2)"
  by (simp add: cequiv_def)

lemma cequiv_on_subseteq:
  assumes "A\<subseteq> B"
  shows "cequiv_on TYPE('a) A \<subseteq> cequiv_on TYPE('a) B"
  by (smt (verit, ccfv_SIG) assms basic_trans_rules(31) case_prodI2
 cequiv_on_def mem_Collect_eq split_conv subsetI)



definition cequivr :: "'a itself \<Rightarrow> (('m,'p) cform \<times> ('m,'p) cform) set"
  where 
"cequivr TYPE('a) = cequiv_on  TYPE('a) UNIV"

lemma cequiv_on_cequivr:
"cequiv_on TYPE('a) s =  cequivr TYPE('a) \<inter> s \<times> s"
  unfolding cequiv_on_def cequivr_def set_eq_iff by auto


lemma NOT_cequiv_cVAR_cDIAM:
 "\<not> (cequiv TYPE('a) (cVAR (a::'p)) (cDIAM (m::'m) fl))"
proof - 
  obtain a0::'a where "True" by simp
  define M where "M = ({a0},(\<lambda> (m::'m) ws::'a list. False), \<lambda> (p::'p) w::'a. True)"
  have "asatis M a0 (cVAR a)" by (simp add: M_def)
  have "\<not> asatis M a0 (cDIAM (m::'m) fl)" 
    by (simp add: M_def)
  show ?thesis unfolding cequiv_def 
    using \<open>\<not> asatis M a0 \<diamondsuit>m fl\<close> \<open>asatis M a0 (cVAR a)\<close> by blast
qed

lemma cDIAM_cequiv_cong:
  assumes 
  1:"\<And>f1 f2. (f1,f2) \<in> set (zip fl1 fl2) \<Longrightarrow> 
           (cequiv TYPE('a) f1 f2) "
  and 2:"length fl1 = length fl2"
shows 
  "cequiv TYPE('a) (cDIAM m fl1) (cDIAM m fl2)" using 2 1
  unfolding cequiv_def
proof (intro allI iffI)
     fix M fix w::'a
    assume l12:"length fl1 = length fl2"
    and "\<And>f1 f2. (f1, f2) \<in> set (zip fl1 fl2) \<Longrightarrow> 
         \<forall>M w. asatis M w f1 = asatis M w f2"
    and s1:"asatis M w (cDIAM m fl1)"

    show "asatis M w (cDIAM m fl2)" unfolding asatis.simps
    proof - 
      from s1 have "w \<in> world M"
        using asatis_in_world by auto     
      from s1 obtain vl where
        lv1fl1:"length vl = length fl1"
        and "rel M m (w # vl)"
        and sfl1:"\<And>x y. (x, y) \<in> set (zip vl fl1) \<Longrightarrow> asatis M x y"
        by auto
      have "length vl = length fl2" using l12 lv1fl1 by simp
      have "\<And> x y. (x,y)\<in> set (zip vl fl2) \<Longrightarrow> asatis M x y"
      proof - 
        fix x y 
        assume xy:"(x,y)\<in> set (zip vl fl2)"
        then obtain n where "n < length vl"
        and "x = nth vl n" and y:"y = nth fl2 n" 
          by (metis fst_conv in_set_zip snd_conv)
        then have "(nth fl1 n,y) \<in> set (zip fl1 fl2)" 
          using in_set_zip l12 lv1fl1 by force
        then have ceq: "cequiv TYPE('a) (nth fl1 n) y " using 1
          by blast
        from sfl1 xy have "asatis M x y" 
          by (metis \<open>cequiv TYPE('a) (fl1 ! n) y\<close> \<open>n < length vl\<close>
         \<open>x = vl ! n\<close> cequiv_def fst_conv in_set_zip lv1fl1 snd_conv)
        then show "asatis M x y" using ceq
          by auto
      qed
      show "w \<in> world M \<and>
    (\<exists>vl. length vl = length fl2 \<and> rel M m (w # vl) \<and> 
     (\<forall>x y. (x, y) \<in> set (zip vl fl2) \<longrightarrow> asatis M x y))"
        using \<open>\<And>y x. (x, y) \<in> set (zip vl fl2) \<Longrightarrow> asatis M x y\<close> 
        \<open>length vl = length fl2\<close> \<open>rel M m (w # vl)\<close> 
        \<open>w \<in> world M\<close> by blast
    qed

next  
    fix M fix w::'a
    assume l12:"length fl1 = length fl2"
    and "\<And>f1 f2. (f1, f2) \<in> set (zip fl1 fl2) \<Longrightarrow> 
\<forall>M w. asatis M w f1 = asatis M w f2"
    and s2:"asatis M w (cDIAM m fl2)"

    show "asatis M w (cDIAM m fl1)" unfolding asatis.simps
    proof - 
      from s2 have "w \<in> world M"
        using asatis_in_world by auto     
      from s2 obtain vl where
        lvfl2:"length vl = length fl2"
        and "rel M m (w # vl)"
        and sfl2:"\<And>x y. (x, y) \<in> set (zip vl fl2) \<Longrightarrow> asatis M x y"
        by auto
      have "length vl = length fl1" using l12 lvfl2 by simp
      have "\<And> x y. (x,y)\<in> set (zip vl fl1) \<Longrightarrow> asatis M x y"
      proof - 
        fix x y 
        assume xy:"(x,y)\<in> set (zip vl fl1)"
        then obtain n where "n < length vl"
        and "x = nth vl n" and y:"y = nth fl1 n" 
          by (metis fst_conv in_set_zip snd_conv)
        then have "(y,nth fl2 n) \<in> set (zip fl1 fl2)" 
          using in_set_zip l12 lvfl2 by fastforce
        then have ceq: "cequiv TYPE('a) y (nth fl2 n)" using 1
          by metis
        from sfl2 xy have "asatis M x y" 
          by (metis \<open>n < length vl\<close> \<open>x = vl ! n\<close> 
           ceq cequiv_def fst_conv in_set_zip lvfl2 snd_conv)
        then show "asatis M x y" using ceq
          by auto
      qed
      show "w \<in> world M \<and>
    (\<exists>vl. length vl = length fl1 \<and> rel M m (w # vl) \<and> 
     (\<forall>x y. (x, y) \<in> set (zip vl fl1) \<longrightarrow> asatis M x y))"
        using \<open>\<And>y x. (x, y) \<in> set (zip vl fl1) \<Longrightarrow> asatis M x y\<close> 
        \<open>length vl = length fl1\<close> \<open>rel M m (w # vl)\<close> 
        \<open>w \<in> world M\<close> by blast
    qed
  qed


lemma asatis_cCONJ: 
"asatis M w (cCONJ f1 f2) \<equiv> asatis M w f1 \<and> asatis M w f2"
  unfolding cCONJ_def asatis.simps 
  by (smt (verit) asatis_in_world)

lemma asatis_cTRUE:
"asatis M w cTRUE \<equiv> w \<in> world M" unfolding asatis.simps cTRUE_def 
  by simp

definition deg_wffs :: "nat \<Rightarrow> ('m,'p) sig => ('m,'p) cform set"
  where 
"deg_wffs n sig = 
{f:: ('m, 'p) cform. deg f \<le> n \<and> wff sig f}"


lemma equi_asatis_restrict_sig:
  assumes 
     weq: "world M2 = world M1"
  and req:"\<And>m vl. m \<in> modal_operators phi \<Longrightarrow> 
              rel M1 m vl = rel M2 m vl"
  and veq:"\<And>p v. p \<in> prop_letters phi \<Longrightarrow> 
         valt M1 p v = valt M2 p v"
shows "\<And>w.  asatis M1 w phi \<longleftrightarrow> asatis M2 w phi"
  using req veq
proof (induction phi)
  case (cVAR x)
  then show ?case unfolding asatis.simps prop_letters.simps
    using weq veq by auto
next
  case cFALSE
  then show ?case unfolding asatis.simps by simp
    
next
  case (cDISJ phi1 phi2)
  then show ?case unfolding asatis.simps
  prop_letters.simps modal_operators.simps
    by auto
next
  case (cNOT phi)
  then show ?case unfolding asatis.simps
  prop_letters.simps modal_operators.simps
    asatis_in_world using weq by auto
next
  case (cDIAM m fl)
  then show ?case
  proof - 
    have " asatis M1 w (cDIAM m fl) \<Longrightarrow>
           asatis M2 w (cDIAM m fl)"
    proof -
      assume "asatis M1 w (cDIAM m fl)"
      then obtain vl0 where 
       len1:"length vl0 = length fl"
      and rel1:"rel M1 m (w # vl0)"
      and sat1: "\<And>x y. (x, y) \<in> set (zip vl0 fl) \<Longrightarrow> asatis M1 x y"
        unfolding asatis.simps by blast
      have "m \<in> modal_operators (cDIAM m fl)"
        unfolding modal_operators.simps by simp
      with rel1 cDIAM 
      have rel2:"rel M1 m (w # vl0)" by meson
      {fix x y
        assume "(x, y) \<in> set (zip vl0 fl)"
        then have 
        ms:"(\<And>m vl.
        m \<in> modal_operators y \<Longrightarrow>
        rel M1 m vl = rel M2 m vl)"
          using cDIAM unfolding modal_operators.simps
          by (meson cDIAM.prems(1) modal_operators_cDIAM_subseteq set_zip_rightD subset_eq)
        have 
        ps:"(\<And>p v. p \<in> prop_letters y \<Longrightarrow>
            valt M1 p v = valt M2 p v)"
          using cDIAM unfolding prop_letters.simps
          by (metis UN_I \<open>(x, y) \<in> set (zip vl0 fl)\<close> list.set_map set_zip_rightD)
        then have "asatis M2 x y" using cDIAM sat1
          by (metis \<open>(x, y) \<in> set (zip vl0 fl)\<close> ms
            set_zip_rightD)
      }
      then show ?thesis unfolding asatis.simps 
        using \<open>asatis M1 w \<diamondsuit>m fl\<close> cDIAM.prems(1) len1 rel2 weq by auto
    qed
    have " asatis M2 w (cDIAM m fl) \<Longrightarrow>
           asatis M1 w (cDIAM m fl)"
    proof -
      assume "asatis M2 w (cDIAM m fl)"
      then obtain vl0 where 
       len1:"length vl0 = length fl"
      and rel1:"rel M2 m (w # vl0)"
      and sat1: "\<And>x y. (x, y) \<in> set (zip vl0 fl) \<Longrightarrow> asatis M2 x y"
        unfolding asatis.simps by blast
      have "m \<in> modal_operators (cDIAM m fl)"
        unfolding modal_operators.simps by simp
      with rel1 cDIAM 
      have rel2:"rel M2 m (w # vl0)" by meson
      {fix x y
        assume "(x, y) \<in> set (zip vl0 fl)"
        then have 
        ms:"(\<And>m vl.
        m \<in> modal_operators y \<Longrightarrow>
        rel M2 m vl = rel M1 m vl)"
          using cDIAM unfolding modal_operators.simps
          by (meson cDIAM.prems(1) modal_operators_cDIAM_subseteq set_zip_rightD subset_eq)
        have 
        ps:"(\<And>p v. p \<in> prop_letters y \<Longrightarrow>
            valt M1 p v = valt M2 p v)"
          using cDIAM unfolding prop_letters.simps
          by (metis UN_I \<open>(x, y) \<in> set (zip vl0 fl)\<close> list.set_map set_zip_rightD)
        then have "asatis M1 x y" using cDIAM sat1
          by (metis \<open>(x, y) \<in> set (zip vl0 fl)\<close> ms
            set_zip_rightD)
      }
      then show ?thesis unfolding asatis.simps 
        using \<open>asatis M2 w (cDIAM m fl)\<close> cDIAM.prems(1) len1 rel2 weq by auto
    qed
    then show ?case 
      using \<open>asatis M1 w (cDIAM m fl) \<Longrightarrow> asatis M2 w (cDIAM m fl)\<close> by blast
qed
qed

definition restrict_sig:
 "restrict_sig sig oprs plts \<equiv>
  ((ops sig \<inter> oprs,arity sig),props sig \<inter> plts)"

lemma restrict_struct_struct:
  assumes "is_struct sig M"
  and "W \<noteq> {}"
  shows "is_struct sig (W, 
  restrict_rel (rel M) W, 
  restrict_valt (valt M) W)"
  using assms unfolding is_struct_def fst_conv snd_conv
restrict_valt_def restrict_rel_def 
  by blast

lemma satis_all_P:
  assumes w1:"w1 \<in> world M1"
   and w2:"w2 \<in> world M2"
   and Pimp: "\<And>phi. P phi \<Longrightarrow> P (cNOT phi)"
   and asm:"\<And>phi. P phi \<Longrightarrow>
        asatis M1 w1 phi \<Longrightarrow> asatis M2 w2 phi"
    and P:"P phi"
  shows
        "asatis M1 w1 phi = asatis M2 w2 phi"
proof - 
  {assume w2phi:"asatis M2 w2 phi"
   and "\<not> asatis M1 w1 phi"
    then have w1nphi:"asatis M1 w1 (cNOT phi)"
      using w1 unfolding asatis.simps by simp
    have "P (cNOT phi)" using Pimp[OF P].
    with asm w1nphi have "asatis M2 w2 (cNOT phi)"
      by metis
    with w2phi have False unfolding asatis.simps by metis
  }
  then show ?thesis using asm P by blast
qed

lemma satis_all_deg_n:
  assumes w1:"w1 \<in> world M1"
   and w2:"w2 \<in> world M2"
   and eqk:"\<And>phi.  phi \<in> deg_wffs k sig \<Longrightarrow>
        asatis M1 w1 phi \<Longrightarrow> asatis M2 w2 phi"
    and deg:" phi \<in> deg_wffs k sig"
  shows
        "asatis M1 w1 phi = asatis M2 w2 phi"
proof - 
  {assume w2phi:"asatis M2 w2 phi"
   and "\<not> asatis M1 w1 phi"
    then have w1nphi:"asatis M1 w1 (cNOT phi)"
      using w1 unfolding asatis.simps by simp
    have "cNOT phi \<in> deg_wffs k sig" unfolding deg.simps 
     
      by (metis (no_types, lifting) deg deg.simps(3) deg_wffs_def mem_Collect_eq wff_cNOT)
    with eqk w1nphi have "asatis M2 w2 (cNOT phi)"
      by metis
    with w2phi have False unfolding asatis.simps by metis
  }
  then show ?thesis using eqk deg by blast
qed

lemma csatis_struct_cVAR:
  assumes "is_struct sig M"
  shows "csatis sig M w (cVAR p) \<equiv> p \<in> props sig \<and> valt M p w"
  by (smt (verit, best) assms csatis_simps(2) is_struct_def)

lemma csatis_struct_cDIAM0:
  assumes "is_struct sig M"
  shows "csatis sig M w (cDIAM m fl) \<equiv>
  \<exists>vl. length vl = length fl \<and> rel M m (w # vl) \<and>
(\<forall>x y. (x,y) \<in> set (zip vl fl) \<longrightarrow> csatis sig M x y)"
  unfolding csatis.simps is_struct_def
  by (smt (verit) Suc_eq_plus1 add_right_imp_eq assms is_struct_def length_Cons list.set_intros(1))

end
