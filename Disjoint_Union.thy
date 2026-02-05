(* Title:        Part of the Modal Model Theory project
 * Content:      Construct disjoint union as in Blackburn et al. 
                 Use this to prove the congruence lemma of triangle formula.
 *)



theory Disjoint_Union
  imports Main Modal_Syntax Modal_Model Modal_Semantics
  "HOL-Library.Countable_Set" "HOL.BNF_Wellorder_Constructions"
begin

definition DU_world where
 "DU_world f dm \<equiv> {(i, w). i \<in> dm \<and> w \<in> world (f i)}"

definition DU_rel where 
 "DU_rel f dm m pl \<equiv> \<exists>i. i \<in> dm \<and> set (map fst pl) = {i} \<and> 
                      rel (f i) m (map snd pl)"

definition DU_valt where
 "DU_valt f dm p w \<equiv> fst w \<in> dm \<and> valt (f (fst w)) p (snd w)"

definition DU where 
 "DU f dm = (DU_world f dm, DU_rel f dm, DU_valt f dm)"

lemma prop_2_3 :
  assumes "fst w \<in> dm"
  shows "asatis (f (fst w)) (snd w) phi \<equiv> asatis (DU f dm) w phi"
  using assms
proof (induction phi  arbitrary: w rule: cform.induct)
  case (cVAR x)
  then show ?case unfolding asatis.simps DU_def fst_conv snd_conv
    DU_world_def mem_Collect_eq DU_valt_def 
    by (simp add: case_prod_beta)
next
  case cFALSE
  then show ?case unfolding asatis.simps by simp
next
  case (cDISJ x1a x2)
  then show ?case unfolding asatis.simps by blast
next
  case (cNOT x)
  then show ?case unfolding asatis.simps DU_def fst_conv snd_conv
    DU_world_def mem_Collect_eq
    by (simp add: case_prod_beta) 
next
  case (cDIAM m fl)
  {assume lhs: "asatis (f (fst w)) (snd w) (cDIAM m fl)"
    define i where "i\<equiv> fst w"
    define wi where "wi \<equiv> snd w"
    have "wi \<in> world (f i)" using asatis_in_world i_def wi_def
      using lhs by force
    with cDIAM have "w \<in> DU_world f dm" using DU_world_def
      using i_def wi_def by fastforce
    from lhs obtain vl where 
    len:" length vl = length fl"
    and rel: " rel (f i) m (wi # vl)"
    and sat:"\<And>v fm. (v,fm) \<in> set (zip vl fl) \<Longrightarrow> asatis (f i) v fm"
      unfolding asatis.simps i_def wi_def by blast
    define vl' where 
    "vl' \<equiv> map (\<lambda>v. (i,v)) vl"
    then have "set (map fst (w # vl')) = {i}" 
      unfolding vl'_def set_eq_iff mem_Collect_eq
      using i_def by auto
    have sndwivl:"(map snd (w # vl')) = (wi # vl)" using wi_def vl'_def 
      by (simp add: list.map_ident_strong)
    then have relsnd:"rel (f i) m (map snd (w # vl'))" using rel 
      by metis
    with sndwivl have "rel (DU f dm) m (w # vl')"
      unfolding DU_def DU_rel_def
      using \<open>set (map fst (w # vl')) = {i}\<close> cDIAM.hyps(2) by auto
    {fix v' fm assume "(v',fm) \<in> set (zip  vl' fl)"
      then have v'i:"fst v' = i" using vl'_def
        by (metis fst_conv in_set_conv_nth length_map nth_map set_zip_leftD)
      then have fstv':"fst v' \<in> dm" 
        by (simp add: cDIAM.hyps(2) i_def)
      have fmfl:"fm \<in> set fl"
        by (metis \<open>(v', fm) \<in> set (zip vl' fl)\<close> set_zip_rightD)
      with cDIAM(1)[OF fmfl fstv'] sat have "asatis (DU f dm) v' fm" 
       by (metis \<open>(v', fm) \<in> set (zip vl' fl)\<close> fst_conv in_set_zip len nth_map snd_conv vl'_def)
     }
     then
     have " asatis (DU f dm) w (cDIAM m fl)" unfolding asatis.simps
       by (metis DU_def \<open>rel (DU f dm) m (w # vl')\<close> \<open>w \<in> DU_world f dm\<close> 
           fst_conv len length_map vl'_def)
   }
 
     {assume rhs:"asatis (DU f dm) w (cDIAM m fl)"
       then have w:"w \<in> DU_world f dm" using asatis_in_world DU_def 
         by (metis fst_conv)
       define i where "i \<equiv> fst w"
       define wi where "wi \<equiv> snd w" 
       have "i \<in> dm" using i_def w DU_world_def
         using cDIAM.hyps(2) by blast
       have wi:"wi \<in> world (f i)" using i_def w DU_world_def 
         by (metis (no_types, lifting) Product_Type.Collect_case_prodD wi_def)
       from rhs obtain vl'
         where 
          len: "length vl' = length fl" and
          rel:"DU_rel f dm m (w # vl')" 
         and sat:"\<And>v fm. (v,fm) \<in> set (zip vl' fl) \<Longrightarrow>
             asatis (DU f dm) v fm" unfolding asatis.simps
         by (metis DU_def fst_conv snd_conv)
       from DU_rel_def have "\<And>v'. v' \<in> set vl' \<Longrightarrow> fst v' = i" 
         by (metis (no_types, lifting) i_def list.set_intros(1)
         prod.collapse rel set_subset_Cons set_zip_leftD singletonD subsetD zip_map_fst_snd)
       with DU_rel_def rel have "rel (f i) m (map snd (w # vl'))" 
         by (metis i_def list.set_intros(1) prod.collapse set_zip_leftD singletonD zip_map_fst_snd)
       then have "rel (f i) m (wi # map snd (vl'))" using wi_def 
         by simp
       define vl where "vl = map snd vl'"
       {fix v fm assume "(v,fm) \<in> set (zip vl fl)" 
         then have fm: "fm \<in> set fl" by (meson set_zip_rightD)
         have "((i,v),fm)\<in> set (zip vl' fl)" using vl_def i_def 
           by (metis \<open>(v, fm) \<in> set (zip vl fl)\<close> \<open>\<And>v'. v' \<in> set vl' \<Longrightarrow> fst v' = i\<close>
          fst_conv in_set_conv_nth in_set_zip length_map nth_map prod_eqI snd_conv)
         have fstdm:"fst (i,v) \<in> dm" 
           by (simp add: \<open>i \<in> dm\<close>)
         from cDIAM(1)[OF fm fstdm] have 
        "asatis (f (fst (i, v))) (snd (i, v)) fm" 
           using \<open>((i, v), fm) \<in> set (zip vl' fl)\<close> sat by blast
        }
        then have "asatis (f (fst w)) (snd w) (cDIAM m fl)" unfolding asatis.simps 
          using len rel wi i_def 
          using \<open>rel (f i) m (wi # map snd vl')\<close> vl_def wi_def by force
      }
  then show ?case 
    using \<open>asatis (f (fst w)) (snd w) (cDIAM m fl) \<Longrightarrow> asatis (DU f dm) w (cDIAM m fl)\<close> by blast
qed

term "R m wl \<equiv> if (hd wl \<noteq> (i,undefined)) then (DU_rel Ms {i. i < n} m wl)
                     else true"
term "W\<equiv>{(i,undefined)} \<union> DU_world Ms {i. i < n}"
term "R \<equiv> \<lambda> m wl. if (hd wl \<noteq> (i,undefined)) then (DU_rel Ms {i. i < n} m wl)
                     else true"


find_consts "?'a \<Rightarrow> ?'a list"
term "upt 2 3"
find_theorems(200) upt "length"


lemma in_world_sat_or_not:
  assumes "w \<in> world M"
  shows "asatis M w f \<or> asatis M w (cNOT f)" 
  using assms by auto


lemma not_satis_and_cNOT:
  shows "\<not> (asatis M w f \<and> asatis M w (cNOT f))"
  by simp

lemma double_neg:
  "asatis M w (cNOT (cNOT f))\<equiv> asatis M  w f" 
  by (smt (verit, best) asatis.simps(4) asatis_in_world)

lemma not_DU_rel:
  assumes "fst w0 \<notin> dm"
  and "w0 \<in> set vl"
shows "\<not>(DU_rel f dm m vl)"
  by (metis DU_rel_def assms(1) assms(2) prod.collapse set_zip_leftD singletonD zip_map_fst_snd)
  
lemma asatis_cDIAM_only_m:
  fixes m0
  assumes sat: "\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) (ws i) (fl ! i)"
  defines "n \<equiv> length fl"
  defines "w0 \<equiv> (n,undefined)"
  defines "W \<equiv> {w0} \<union> DU_world Ms {i. i < n}"
  defines "wsl \<equiv> map (\<lambda>i. (i, ws i)) (upt 0 n)"
  defines "R \<equiv> \<lambda> m wl. 
 if (hd wl \<noteq> w0) then (DU_rel Ms {i. i < n} m wl)
                     else m = m0 \<and> wl = w0 # wsl "
  defines "V \<equiv> DU_valt Ms {i. i < n}"
  defines "M \<equiv> (W,R,V)"
  
shows "asatis M w0 (cDIAM m0 fl) \<and> 
  (\<forall>m fl. m \<noteq> m0 \<longrightarrow> \<not>asatis M w0 (cDIAM m fl))"
proof -
  have rw0:"\<And>m vl. R m (w0 # vl) \<Longrightarrow> m = m0" unfolding R_def
    by force
  {fix m fl assume "m \<noteq> m0" then 
    have "\<not>asatis M w0 (cDIAM m fl)" unfolding asatis.simps rw0 
    using M_def rw0 by auto
} 
  have "R m0 (w0 # wsl)" unfolding R_def by auto
  have "length wsl = n" unfolding n_def wsl_def by auto
  {fix i assume "i < n" then have "wsl ! i = (i,ws i)" using wsl_def
   by auto
}
  
  {fix wi f assume "(wi,f) \<in> set (zip wsl fl)" 
    define i where "i \<equiv> fst wi"
    then have "i < length fl"
      by (metis \<open>(wi, f) \<in> set (zip wsl fl)\<close> \<open>\<And>i. i < n \<Longrightarrow> wsl ! i = (i, ws i)\<close>
      \<open>length wsl = n\<close> fst_conv in_set_zip)
    then have "asatis (Ms (fst wi)) (snd wi) f" using sat 
      by (metis \<open>(wi, f) \<in> set (zip wsl fl)\<close> \<open>\<And>i. i < n \<Longrightarrow> wsl ! i = (i, ws i)\<close> 
              \<open>length wsl = n\<close> fst_conv in_set_zip snd_conv)
   }
  have "\<And>wi f. (wi,f) \<in> set (zip wsl fl) \<Longrightarrow>
                asatis (DU Ms {i. i < n}) wi f"
    using  prop_2_3 
    by (metis \<open>\<And>i. i < n \<Longrightarrow> wsl ! i = (i, ws i)\<close> 
    \<open>\<And>wi fa. (wi, fa) \<in> set (zip wsl fl) \<Longrightarrow> asatis (Ms (fst wi)) (snd wi) fa\<close> 
    \<open>length wsl = n\<close> fst_conv in_set_zip mem_Collect_eq)
  have wss:"world (DU Ms  {i. i < n}) \<subseteq> world M" unfolding M_def
    by (simp add: DU_def W_def subsetI)
  {fix f w
   have "w \<in> DU_world Ms {i. i < n} \<Longrightarrow>
     asatis (DU Ms {i. i < n}) w f \<equiv> asatis M w f"
   proof (induction f arbitrary: w )
     case (cVAR x)
     then show ?case 
       by (metis DU_def M_def V_def W_def asatis.simps(2) 
           fst_conv insert_iff insert_is_Un snd_conv) 
   next
     case cFALSE
     then show ?case   by auto
   next
     case (cDISJ f1 f2)
     then show ?case
       by (metis asatis.simps(3))
   next
     case (cNOT f) then show ?case 
       by (simp add: DU_def M_def W_def)
     
   next
     case (cDIAM m fl)
     {assume lhs: " asatis (DU Ms {i. i < n}) w (cDIAM m fl)"
       then have "w \<in> DU_world Ms {i. i < n}" using asatis_in_world DU_def
         using cDIAM.hyps(2) by blast
       then have wnotw0: "w \<noteq> w0" 
         by (metis (no_types, lifting) DU_world_def Product_Type.Collect_case_prodD fst_conv 
        less_not_refl mem_Collect_eq w0_def)
       from lhs obtain vl where 
        len: "length vl = length fl" and
        rel : "DU_rel Ms {i. i < n} m (w # vl)" and 
        sat: "\<And>v f. (v,f) \<in> set (zip vl fl) \<Longrightarrow> asatis (DU Ms {i. i < n}) v f"
         unfolding asatis.simps
         by (metis DU_def fst_conv snd_conv)
       then have "R  m (w # vl)" unfolding R_def
         using wnotw0 by auto
       {fix v f assume "(v,f) \<in> set (zip vl fl)"
         then have "asatis M v f"
           by (metis DU_def asatis_in_world cDIAM.hyps(1) fst_conv sat set_zip_rightD)
         
       }
       then have "asatis M w (cDIAM m fl)" 
         using M_def \<open>R m (w # vl)\<close> len lhs wss by auto
     }
     {assume rhs: "asatis M w (cDIAM m fl)"
     then have "w \<in> DU_world Ms {i. i < n}" using asatis_in_world DU_def
         using cDIAM.hyps(2) by blast
       then have wnotw0: "w \<noteq> w0" 
         by (metis (no_types, lifting) DU_world_def Product_Type.Collect_case_prodD fst_conv 
        less_not_refl mem_Collect_eq w0_def)
       from rhs obtain vl where 
        len: "length vl = length fl" and
        rel : "DU_rel Ms {i. i < n} m (w # vl)" and 
        sat: "\<And>v f. (v,f) \<in> set (zip vl fl) \<Longrightarrow> asatis M v f"
         unfolding asatis.simps 
         using M_def R_def wnotw0 by auto
       then have "R  m (w # vl)" unfolding R_def
         using wnotw0 by auto
       have "set vl \<subseteq> world M" using asatis_in_world sat 
         by (metis in_set_impl_in_set_zip1 len subsetI)
       have w0notvl: "w0 \<notin> set vl" using rel not_DU_rel w0_def
         by (metis fst_conv less_not_refl list.set_intros(2) mem_Collect_eq)
       {fix v f assume "(v,f) \<in> set (zip vl fl)"
         then have "asatis (DU Ms {i. i < n}) v f" using cDIAM sat
           w0notvl
           by (metis M_def W_def asatis_in_world fst_conv insert_iff 
               insert_is_Un set_zip_leftD set_zip_rightD)
       }
       then have "asatis (DU Ms {i. i < n}) w (cDIAM m fl)" 
         using M_def \<open>R m (w # vl)\<close> len rhs wss
         by (metis DU_def asatis.simps(5) cDIAM.hyps(2) fst_conv rel snd_conv)
     }
     then show ?case
       using \<open>asatis (DU Ms {i. i < n}) w (cDIAM m fl) \<Longrightarrow> asatis M w (cDIAM m fl)\<close> by blast
   qed
     
   }
   then have "\<And>wi f. (wi,f) \<in> set (zip wsl fl) \<Longrightarrow>
                asatis M wi f" 
     by (metis DU_def \<open>\<And>wi fa. (wi, fa) \<in> set (zip wsl fl) \<Longrightarrow> asatis (DU Ms {i. i < n}) wi fa\<close> 
     asatis_in_world fst_conv)
   then have "asatis M w0  (cDIAM m0 fl)"
     using M_def W_def \<open>R m0 (w0 # wsl)\<close> \<open>length wsl = n\<close> n_def by auto
   show ?thesis
     using \<open>\<And>ma fla. ma \<noteq> m0 \<Longrightarrow> \<not> asatis M w0 \<diamondsuit>ma fla\<close> \<open>asatis M w0 \<diamondsuit>m0 fl\<close> by argo
 qed


definition copy_rel where 
"copy_rel f M \<equiv> \<lambda> m wl. \<exists>wl0. wl = map f wl0 \<and> rel M m wl0"

definition copy_valt where 
"copy_valt f M \<equiv> \<lambda>p v. \<exists>v0. v = f v0 \<and> valt M p v0"

definition copy where
"copy f M \<equiv> (f ` world M, copy_rel f M, copy_valt f M)"


term "inj"
lemma copy_asatis :
  assumes "inj i"
  shows "asatis M w f \<equiv> asatis (copy i M) (i w) f"
proof (induction f arbitrary: w)
  case (cVAR x)
  then show ?case unfolding asatis.simps fst_conv snd_conv copy_def
  copy_valt_def using inj_def
    by (metis assms inj_image_mem_iff)
next
  case cFALSE
  then show ?case
    by simp
next
  case (cDISJ f1 f2)
  then show ?case   by auto
next
  case (cNOT f)
  then show ?case  
    by (simp add: assms copy_def inj_image_mem_iff)
next
  case (cDIAM m fl)
  {assume lhs: "asatis M w (cDIAM m fl) "
    then obtain vl where 
   len : "length vl = length fl" and 
   rel : "rel M m (w # vl)" and 
   sat : "\<And>v f. (v,f) \<in> set (zip vl fl) \<Longrightarrow> asatis M v f"
      unfolding asatis.simps  by blast
    then have "rel (copy i M) m (i w # map i vl) " unfolding copy_def copy_rel_def
     inj_def by force
    from sat asatis_in_world have "set vl \<subseteq> world M" 
      by (metis in_set_impl_in_set_zip1 len subsetI)
    {fix iv f assume "(iv, f) \<in> set (zip (map i vl) fl)" 
      have f: "f \<in> set fl"
        by (metis \<open>(iv, f) \<in> set (zip (map i vl) fl)\<close> set_zip_rightD)
      from cDIAM[OF f] sat
      have "asatis (copy i M) iv f" 
        by (metis \<open>(iv, f) \<in> set (zip (map i vl) fl)\<close> 
           fst_conv in_set_zip length_map nth_map snd_conv)  }
    then have "asatis (copy i M) (i w) (cDIAM m fl)" 
      by (metis (no_types, lifting) \<open>rel (copy i M) m (i w # map i vl)\<close> asatis.simps(5) assms 
   copy_def inj_image_mem_iff len length_map lhs split_pairs)
  }
  {assume rhs: "asatis (copy i M) (i w) (cDIAM m fl)" 
   then obtain ivl where 
   len : "length ivl = length fl" and 
   rel : "rel (copy i M) m (i w # ivl)" and 
   sat : "\<And>iv f. (iv,f) \<in> set (zip ivl fl) \<Longrightarrow> asatis (copy i M) iv f"
     unfolding asatis.simps by blast
   then obtain vl where 
   "ivl = map i vl" and "rel M m (w # vl)" unfolding copy_def copy_rel_def using assms 
     using inj_onD by fastforce
   from sat asatis_in_world have "set vl \<subseteq> world M" 
      by (metis (no_types, opaque_lifting) \<open>ivl = map i vl\<close> assms copy_def in_set_impl_in_set_zip1 
      inj_image_mem_iff len list.set_map split_pairs subset_eq)
    {fix v f assume "(v, f) \<in> set (zip vl fl)" 
      have f: "f \<in> set fl"
        by (metis \<open>(v, f) \<in> set (zip vl fl)\<close> set_zip_rightD)
      from cDIAM[OF f] sat
      have "asatis M v f" 
        by (metis \<open>(v, f) \<in> set (zip vl fl)\<close> \<open>ivl = map i vl\<close>
           fst_conv in_set_zip len nth_map snd_conv)
       }
       then have "asatis M w (cDIAM m fl) " 
         by (metis (no_types, opaque_lifting) \<open>ivl = map i vl\<close> \<open>rel M m (w # vl)\<close> asatis.simps(5) 
      assms copy_def fst_conv inj_image_mem_iff len length_map rhs)
  }
  then show ?case
    using \<open>asatis M w (cDIAM m fl) \<Longrightarrow> asatis (copy i M) (i w) (cDIAM m fl)\<close> by blast
  
qed


lemma  infinite_inj_back_lemma:
  fixes X :: "'a set"
  assumes "infinite X" "countable Y" "Y \<noteq> {}"
  shows "\<exists>f. bij_betw f (Y \<times> X) X"
  apply (subst card_of_ordIso)
  apply (rule card_of_Times_infinite[OF assms(1,3), THEN conjunct2])
  by (meson assms card_of_ordLeqI countableE 
  infinite_iff_card_of_nat iso_tuple_UNIV_I ordLeq_transitive)

lemma infinite_inj_back:
assumes "infinite (UNIV::'a set)"
shows "\<exists>i::(nat \<times> 'a) \<Rightarrow> 'a. inj i" using infinite_inj_back_lemma
  by (metis UNIV_Times_UNIV assms bij_betw_def countableI_type empty_not_UNIV)
  
  

lemma fl_satisfiable_exists_family:
  assumes sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  shows "\<exists>Ms ws. \<forall>i. i < length fl \<longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
proof -
  {fix i  assume "i < length fl" 
    then have "fl ! i \<in> set fl" by auto
    from sat[OF this] obtain Mw where "asatis (fst Mw) ((snd Mw)::'a) (fl ! i)"
      by force
    then have "\<exists> Mw. asatis (fst Mw) ((snd Mw)::'a) (fl ! i) "
    by meson
}
  then show ?thesis by meson
qed
  


lemma list_satis_not_exist_cDIAM_FALSE0:
  assumes "f \<in> set fl"
  and "\<And>M w::'a. \<not>asatis M w f"
shows "\<And>M w::'a. \<not>asatis M w (cDIAM m fl)" unfolding asatis.simps
  by (meson assms(1) assms(2) in_set_impl_in_set_zip2)

lemma not_satisfiable_iff_FALSE:
  assumes  "\<And>M w::'a. \<not>asatis M w f"
  shows "cequiv TYPE('a) f cFALSE" unfolding cequiv_def asatis.simps 
  using assms by auto

lemma list_satis_not_exist_cDIAM_FALSE:
  assumes "f \<in> set fl"
  and "\<And>M w::'a. \<not>asatis M w f"
shows  "cequiv TYPE('a) (cDIAM m fl) cFALSE" 
  using list_satis_not_exist_cDIAM_FALSE0 not_satisfiable_iff_FALSE
 by (metis assms(1) assms(2))

lemma infinite_cDIAM_cequiv_ops_eq:
  assumes "infinite (UNIV::'a set)"
  and sat: "\<And>i. i < length fl1 \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl1 ! i)"
  and "cequiv TYPE('a) (cDIAM m1 fl1) (cDIAM m2 fl2)"
shows "m1 = m2"
proof (rule ccontr)
  assume "m1 \<noteq> m2"
  from asatis_cDIAM_only_m obtain M0 w0 where
  sat0:"asatis M0 (w0:: nat \<times> 'a) (cDIAM m1 fl1)" and
  " (\<forall>m fl. m \<noteq> m1 \<longrightarrow> \<not>asatis M0 w0 (cDIAM m fl))"
    by (metis (no_types, lifting) sat)
  then have "\<not>asatis M0 w0 (cDIAM m2 fl2)" 
    using \<open>m1 \<noteq> m2\<close> by presburger
  from infinite_inj_back obtain i :: "(nat \<times> 'a) \<Rightarrow> 'a" where "inj i"
    using assms(1) by blast
  from copy_asatis show False 
    by (metis \<open>\<And>thesis. (\<And>i. inj i \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
\<open>\<not> asatis M0 w0 \<diamondsuit>m2 fl2\<close> assms(3) cequiv_def sat0)
qed


lemma cDIAM_cequiv_cases:
  assumes "infinite (UNIV::'a set)"
  and "cequiv TYPE('a) (cDIAM m1 fl1) (cDIAM m2 fl2)"
shows "(cequiv TYPE('a) (cDIAM m1 fl1) cFALSE) \<or> m1 = m2"
proof -
  consider 
  (c1) "\<And>f. f \<in> set fl1 \<Longrightarrow> \<exists>M w::'a. asatis M w f" |
  (c2) "\<exists>f. f \<in> set fl1 \<and> (\<forall>M w::'a. \<not>asatis M w f)" 
    by blast
  then show ?thesis proof cases
    case c1
    then show ?thesis using infinite_cDIAM_cequiv_ops_eq 
     fl_satisfiable_exists_family
      by (metis assms(1) assms(2))
  next
    case c2
    then show ?thesis using list_satis_not_exist_cDIAM_FALSE 
      by metis
  qed
qed

lemma in_zip_ith :
  assumes "length l1  = length l2"
  shows 
 "(a,b) \<in> set( zip l1 l2) \<equiv>  \<exists>i. i < length l1 \<and> a = l1 ! i \<and> b = l2 ! i"
  by (smt (verit, best) assms eq_fst_iff in_set_zip prod.sel(2))



lemma csatis_fl_cong_lemma:
  fixes fl gl m0
  defines "n \<equiv> length fl"
  assumes j:"j < n"
  and lenglfl: "length gl = length fl"
  defines "g \<equiv> gl ! j"
  assumes "\<And>i. i < n \<Longrightarrow> asatis (Ms i) (ws i) (fl ! i)"
  and "\<not>asatis (Ms j) (ws j) g"
  defines "uM \<equiv> DU Ms {i. i < n}"
  defines "w0 \<equiv> (n,undefined)"
  defines "W \<equiv> {w0} \<union> DU_world Ms {i. i < n}"
  defines "wsl \<equiv> map (\<lambda>i. (i, ws i)) (upt 0 n)"
  defines "R \<equiv> \<lambda> m wl. 
 if (hd wl \<noteq> w0) then (DU_rel Ms {i. i < n} m wl)
                     else m = m0 \<and> wl = w0 # wsl "
  defines "V \<equiv> DU_valt Ms {i. i < n}"
  defines "M \<equiv> (W,R,V)"
  shows "asatis M w0 (cDIAM m0 fl) \<and> \<not>asatis M w0 (cDIAM m0 gl) \<and>
       (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis M w0 (cDIAM m' l))"
proof - 
  {fix i assume "i < n" 
    have "asatis uM (i, ws i) (fl ! i)"
      using prop_2_3
      by (metis CollectI \<open>i < n\<close> assms(5) fst_conv snd_conv uM_def)
  }
  
  {fix f w
   have "w \<in> DU_world Ms {i. i < n} \<Longrightarrow>
     asatis (DU Ms {i. i < n}) w f \<equiv> asatis M w f"
   proof (induction f arbitrary: w )
  case (cVAR x)
     then show ?case 
       by (metis DU_def M_def V_def W_def asatis.simps(2) 
           fst_conv insert_iff insert_is_Un snd_conv) 
   next
     case cFALSE
     then show ?case   by auto
   next
     case (cDISJ f1 f2)
     then show ?case
       by (metis asatis.simps(3))
   next
     case (cNOT f) then show ?case 
       by (simp add: DU_def M_def W_def)
     
   next
     case (cDIAM m fl)
     {assume lhs: " asatis (DU Ms {i. i < n}) w (cDIAM m fl)"
       then have "w \<in> DU_world Ms {i. i < n}" using asatis_in_world DU_def
         using cDIAM.hyps(2) by blast
       then have wnotw0: "w \<noteq> w0" 
         by (metis (no_types, lifting) DU_world_def Product_Type.Collect_case_prodD fst_conv 
        less_not_refl mem_Collect_eq w0_def)
       from lhs obtain vl where 
        len: "length vl = length fl" and
        rel : "DU_rel Ms {i. i < n} m (w # vl)" and 
        sat: "\<And>v f. (v,f) \<in> set (zip vl fl) \<Longrightarrow> asatis (DU Ms {i. i < n}) v f"
         unfolding asatis.simps
         by (metis DU_def fst_conv snd_conv)
       then have "R  m (w # vl)" unfolding R_def
         using wnotw0 by auto
       {fix v f assume "(v,f) \<in> set (zip vl fl)"
         then have "asatis M v f"
           by (metis DU_def asatis_in_world cDIAM.hyps(1) fst_conv sat set_zip_rightD)
         
       }
       then have "asatis M w (cDIAM m fl)" 
         using M_def \<open>R m (w # vl)\<close> len lhs 
         using W_def cDIAM.hyps(2) by auto
     }
     {assume rhs: "asatis M w (cDIAM m fl)"
     then have "w \<in> DU_world Ms {i. i < n}" using asatis_in_world DU_def
         using cDIAM.hyps(2) by blast
       then have wnotw0: "w \<noteq> w0" 
         by (metis (no_types, lifting) DU_world_def Product_Type.Collect_case_prodD fst_conv 
        less_not_refl mem_Collect_eq w0_def)
       from rhs obtain vl where 
        len: "length vl = length fl" and
        rel : "DU_rel Ms {i. i < n} m (w # vl)" and 
        sat: "\<And>v f. (v,f) \<in> set (zip vl fl) \<Longrightarrow> asatis M v f"
         unfolding asatis.simps 
         using M_def R_def wnotw0 by auto
       then have "R  m (w # vl)" unfolding R_def
         using wnotw0 by auto
       have "set vl \<subseteq> world M" using asatis_in_world sat 
         by (metis in_set_impl_in_set_zip1 len subsetI)
       have w0notvl: "w0 \<notin> set vl" using rel not_DU_rel w0_def
         by (metis fst_conv less_not_refl list.set_intros(2) mem_Collect_eq)
    
       {fix v f assume "(v,f) \<in> set (zip vl fl)"
         then have "asatis (DU Ms {i. i < n}) v f" using cDIAM sat
           w0notvl
           by (metis M_def W_def asatis_in_world fst_conv insert_iff 
               insert_is_Un set_zip_leftD set_zip_rightD)
       }
       then have "asatis (DU Ms {i. i < n}) w (cDIAM m fl)" 
         using M_def \<open>R m (w # vl)\<close> len rhs  DU_def asatis.simps(5) cDIAM.hyps(2) 
fst_conv rel snd_conv
         by metis
     }
     then show ?case
       using \<open>asatis (DU Ms {i. i < n}) w (cDIAM m fl) \<Longrightarrow> asatis M w (cDIAM m fl)\<close> by blast
   qed
   
 }
  {fix i assume "i < n" 
    have "asatis M (i, ws i) (fl ! i)"
      
      by (metis DU_def \<open>\<And>i. i < n \<Longrightarrow> asatis uM (i, ws i) (fl ! i)\<close> 
\<open>\<And>wa f. wa \<in> DU_world Ms {i. i < n} \<Longrightarrow> asatis (DU Ms {i. i < n}) wa f \<equiv> asatis M wa f\<close> \<open>i < n\<close> 
     asatis_in_world fst_conv uM_def)
  }
  have Rw0wsl:"R m0 (w0 # wsl)" using R_def by auto
  have lenwsl:"length wsl = length fl"
    by (simp add: n_def wsl_def)
  have "\<And> i. i < length fl \<Longrightarrow> wsl ! i = (i, ws i)" 
    using lenwsl wsl_def by auto
  {fix i  assume "i < length fl" 
    then have "asatis M (i,ws i) (fl ! i)" 
      using \<open>\<And>i. i < n \<Longrightarrow> asatis M (i, ws i) (fl ! i)\<close> n_def by force }
  {fix w f assume "(w,f) \<in> set (zip wsl fl)" 
    then have "asatis M w f" 
      by (metis \<open>\<And>i. i < length fl \<Longrightarrow> asatis M (i, ws i) (fl ! i)\<close>
   \<open>\<And>i. i < length fl \<Longrightarrow> wsl ! i = (i, ws i)\<close> fst_conv in_set_zip snd_conv)
  }
  have "asatis M w0 (cDIAM m0 fl)" using M_def R_def V_def W_def asatis_cDIAM_only_m assms(5) 
    n_def w0_def wsl_def
   lenwsl Rw0wsl
    using \<open>\<And>wa fa. (wa, fa) \<in> set (zip wsl fl) \<Longrightarrow> asatis M wa fa\<close> by force
  have 
   "\<And>wl. R m0 (w0 # wl) \<Longrightarrow> wl = wsl" using R_def by simp
  have " ((j,ws j), g) \<in> set ( zip wsl gl)" 
    using g_def in_set_zip j lenglfl n_def wsl_def by fastforce
  {fix l:: "('a, 'b) cform list" and m' assume "length l \<noteq> length fl"
    then have "\<not>asatis M w0 (cDIAM m' l)" 
      using M_def R_def lenwsl by auto
  }
  have "\<not>asatis M (j,ws j) g"
    by (metis DU_def \<open>\<And>i. i < n \<Longrightarrow> asatis uM (i, ws i) (fl ! i)\<close>
       \<open>\<And>wa f. wa \<in> DU_world Ms {i. i < n} \<Longrightarrow> asatis (DU Ms {i. i < n}) wa f \<equiv> asatis M wa f\<close>
      asatis_in_world assms(6) fst_conv j mem_Collect_eq prop_2_3 snd_conv uM_def)
  then show ?thesis 
    using M_def \<open>((j, ws j), g) \<in> set (zip wsl gl)\<close> \<open>\<And>wl. R m0 (w0 # wl) \<Longrightarrow> wl = wsl\<close> 
  \<open>asatis M w0 \<diamondsuit>m0 fl\<close> 
    using \<open>\<And>m'a l. length l \<noteq> length fl \<Longrightarrow> \<not> asatis M w0 \<diamondsuit>m'a l\<close> by auto
qed



lemma infinite_struct_back_lemma:
  assumes "infinite (UNIV:: 'a set)"
  shows "\<exists>Ma i:: nat \<times> 'a \<Rightarrow> 'a. 
 (\<forall>w. asatis M w f = asatis Ma (i w) f)" 
  using copy_asatis 
  by (metis assms infinite_inj_back)



lemma infinite_struct_back_lemma1:
  assumes "infinite (UNIV:: 'a set)"
  and "asatis M (w::nat \<times> 'a) f"
  and "\<not>asatis M (w::nat \<times> 'a) g"
shows "\<exists>Ma wa::'a. asatis Ma wa f \<and> \<not>asatis Ma wa g"
  by (meson assms(1) assms(2) assms(3) copy_asatis infinite_inj_back)


lemma infinite_struct_back_lemma1':
  assumes "infinite (UNIV:: 'a set)"
  and "asatis M (w::nat \<times> 'a) f"
  and "\<not>asatis M (w::nat \<times> 'a) g"
  and "(\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis M w (cDIAM m' l))"
shows "\<exists>Ma wa::'a. asatis Ma wa f \<and> \<not>asatis Ma wa g \<and>
   (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis Ma wa (cDIAM m' l))"
  using assms(1) assms(2) assms(3) assms(4)
  by (metis copy_asatis infinite_inj_back)

lemma csatis_fl_cong_lemma_packed:
  assumes j:"j < length fl"
  and len:"length gl = length fl"
  and sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "\<not>asatis (Ms j) (ws j) (gl ! j)"
shows "\<exists>M w0::nat \<times> 'a. asatis M w0 (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl) \<and>
    (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis M w0 (cDIAM m' l))
"
  using csatis_fl_cong_lemma[OF j len, of Ms ws m0]
  using assms(4) sat by blast


lemma csatis_fl_cong_lemma_packed_same_type:
  assumes j:"j < length fl"
  and len:"length gl = length fl"
  and sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "\<not>asatis (Ms j) (ws j) (gl ! j)"
  and "infinite (UNIV::'a set)"
shows "\<exists>M w0::'a. asatis M w0 (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl) "
proof - 
  obtain M w0 where 
  "asatis M (w0::nat \<times> 'a) (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl)" using csatis_fl_cong_lemma_packed
    by (metis assms(4) j len sat)
  then show ?thesis using infinite_struct_back_lemma1
    using assms(5) by blast
qed


lemma all_asatis_cDIAM_asatis:
  assumes sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "infinite (UNIV::'a set)"
  shows "\<exists>M w0::'a. asatis M w0 (cDIAM m0 fl) "
proof - 
  {assume "fl = []" then have ?thesis using asatis_empty_cDIAM
    by auto
}
  {assume "fl \<noteq> []" 
   define gl where "gl :: ('b, 'c) cform list \<equiv> replicate (length fl) cFALSE"
   then have "length gl = length fl" by simp
   have "gl ! 0 = cFALSE" using gl_def by (simp add: \<open>fl \<noteq> []\<close>)
   have ?thesis using
      
     csatis_fl_cong_lemma_packed_same_type[of 0 fl "gl" Ms ws m0]
   
     by (metis \<open>fl \<noteq> []\<close> \<open>gl ! 0 = cFALSE\<close> \<open>length gl = length fl\<close> asatis.simps(1) assms(2)
   length_greater_0_conv sat) }
  then show ?thesis
    using \<open>fl = [] \<Longrightarrow> \<exists>M w0. asatis M w0 \<diamondsuit>m0 fl\<close> by blast
qed

lemma csatis_fl_cong_lemma_packed_same_type':
  assumes j:"j < length fl"
  and len:"length gl = length fl"
  and sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "\<not>asatis (Ms j) (ws j) (gl ! j)"
  and "infinite (UNIV::'a set)"
shows "\<exists>M w0::'a. asatis M w0 (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl) \<and> 
   (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis M w0 (cDIAM m' l))
"
proof - 
  obtain M w0 where 
  "asatis M (w0::nat \<times> 'a) (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl) \<and>
   (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not>asatis M w0 (cDIAM m' l))" using csatis_fl_cong_lemma_packed
    by (metis assms(4) j len sat)
  then show ?thesis using infinite_struct_back_lemma1'
    using assms(5) 
    by (meson copy_asatis infinite_inj_back)
qed



lemma sat_family_construct_lemma:
  assumes sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  and "j < length fl"
  and "asatis M (w::'a) (fl ! j)"
  and "\<not>asatis M w g"
shows "\<exists>Ms ws. 
    \<not>asatis (Ms j) (ws j::'a) g \<and>
    (\<forall>i. i < length fl \<longrightarrow> asatis (Ms i) (ws i) (fl ! i)) "
proof -
  {fix i assume "i < length fl"
    then have "\<exists>Mw. asatis (fst Mw) (snd Mw :: 'a) (fl ! i)"
      using sat by simp
  }
  then obtain Mws where
   "\<forall>i. i < length fl \<longrightarrow> 
   asatis (fst (Mws i)) (snd (Mws i) :: 'a) (fl ! i)
"  by meson
  define Ms where "Ms \<equiv> \<lambda>i. if i \<noteq> j then (fst o Mws) i else M"
  define ws where "ws \<equiv> \<lambda>i. if i \<noteq> j then (snd o Mws) i else w"
  then have 
   "\<not>asatis (Ms j) (ws j) g \<and>
    (\<forall>i. i < length fl \<longrightarrow> asatis (Ms i) (ws i) (fl ! i))"
    by (simp add: Ms_def \<open>\<forall>i<length fl. asatis (fst (Mws i)) (snd (Mws i)) (fl ! i)\<close> 
      assms(3) assms(4))
  then show ?thesis by auto
qed


lemma infinite_csatis_fl_cong_lemma:
  assumes "infinite (UNIV:: 'a set)"
  and sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  and sat':"\<And>g. g \<in> set gl \<Longrightarrow> \<exists>M w::'a. asatis M w g"
  and len:"length fl = length gl"
  and "cequiv TYPE('a) (cDIAM m0 fl) (cDIAM m0 gl)"
shows 
   "\<And>j. j < length fl \<Longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)"
proof (rule ccontr)
  fix j assume j:"j < length fl" 
  and "\<not> cequiv TYPE('a) (fl ! j) (gl ! j)"
  {fix M w assume
   "asatis M (w::'a) (fl ! j)" and "\<not>asatis M w (gl ! j)"
    then obtain Ms ws where 
    "\<And>i . i < length fl \<Longrightarrow> asatis (Ms i) ((ws i) :: 'a) (fl ! i)"
    and "\<not>asatis (Ms j) (ws j) (gl ! j)" 
      using sat_family_construct_lemma 
      by (metis (full_types) \<open>j < length fl\<close> sat)
    then obtain M w0 where 
     "asatis M (w0::'a) (cDIAM m0 fl) \<and> 
   \<not>asatis M w0 (cDIAM m0 gl)"
      using csatis_fl_cong_lemma_packed_same_type[of j fl gl Ms ws,OF j ]
      using assms(1) len by presburger
    then have False
      by (metis assms(5) cequiv_def)
  }
  {fix M w assume
   "asatis M (w::'a) (gl ! j)" and "\<not>asatis M w (fl ! j)"
    then obtain Ms ws where 
    "\<And>i . i < length gl \<Longrightarrow> asatis (Ms i) ((ws i) :: 'a) (gl ! i)"
    and "\<not>asatis (Ms j) (ws j) (fl ! j)" 
      using sat_family_construct_lemma sat 
      by (metis (full_types) j len sat')
    then obtain M w0 where 
     "asatis M (w0::'a) (cDIAM m0 gl) \<and> 
   \<not>asatis M w0 (cDIAM m0 fl)"
      using csatis_fl_cong_lemma_packed_same_type[of j gl fl Ms ws, OF _ len ]
     assms(1) len
      using j by presburger
    then have False
      by (metis assms(5) cequiv_def)}
  then show False using cequiv_def 
    using \<open>\<And>w M. \<lbrakk>asatis M w (fl ! j); \<not> asatis M w (gl ! j)\<rbrakk> \<Longrightarrow> False\<close> 
\<open>\<not> cequiv TYPE('a) (fl ! j) (gl ! j)\<close> by blast
qed


lemma infinite_csatis_fl_cong_eq_length:
  assumes "infinite (UNIV:: 'a set)"
  and len:"length fl = length gl"
  and "cequiv TYPE('a) (cDIAM m0 fl) (cDIAM m0 gl)"
shows 
   "(\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)) \<or> 
   cequiv TYPE('a) (cDIAM m0 fl) cFALSE "
proof -
  {assume sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  and sat':"\<And>g. g \<in> set gl \<Longrightarrow> \<exists>M w::'a. asatis M w g"
    then have  "\<And>j. j < length fl \<Longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)"
      using infinite_csatis_fl_cong_lemma
      by (metis assms(1) assms(3) len)
  }
  {assume
    sat:"\<exists>f. f \<in> set fl \<and> (\<forall>M w::'a. \<not>asatis M w f)"
    then have " cequiv TYPE('a) (cDIAM m0 fl) cFALSE"using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  {assume
    sat:"\<exists>f. f \<in> set gl \<and> (\<forall>M w::'a. \<not>asatis M w f)"
    then have " cequiv TYPE('a) (cDIAM m0 gl) cFALSE"using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  show ?thesis 
    by (metis \<open>\<And>j. \<lbrakk>\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w. asatis M w f; \<And>g. g \<in> set gl \<Longrightarrow> \<exists>M w. asatis M w g;

  j < length fl\<rbrakk> \<Longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)\<close> 
\<open>\<exists>f. f \<in> set fl \<and> (\<forall>M w. \<not> asatis M w f) \<Longrightarrow>
 cequiv TYPE('a) (cDIAM m0 fl) cFALSE\<close> \<open>\<exists>f. f \<in> set gl \<and>
 (\<forall>M w. \<not> asatis M w f) \<Longrightarrow> cequiv TYPE('a) (cDIAM m0 gl) cFALSE\<close>
 asatis.simps(1) assms(3) cequiv_def)
qed

lemma all_asatis_cDIAM_asatis':
  assumes sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "infinite (UNIV::'a set)"
shows "\<exists>M w0::'a. asatis M w0 (cDIAM m0 fl) \<and>
  (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not> asatis M w0 (cDIAM m' l))"
proof - 
  {assume "fl = []" then have ?thesis using cDIAM_empty_asatis_exists0'
   by metis
}
  {assume "fl \<noteq> []" 
   define gl where "gl :: ('b, 'c) cform list \<equiv> replicate (length fl) cFALSE"
   then have "length gl = length fl" by simp
   have "gl ! 0 = cFALSE" using gl_def by (simp add: \<open>fl \<noteq> []\<close>)
   have ?thesis using
      
     csatis_fl_cong_lemma_packed_same_type'[of 0 fl "gl" Ms ws m0]
   
     by (metis \<open>fl \<noteq> []\<close> \<open>gl ! 0 = cFALSE\<close> \<open>length gl = length fl\<close> asatis.simps(1) assms(2)
   length_greater_0_conv sat) }
  then show ?thesis 
    using \<open>fl = [] \<Longrightarrow> \<exists>M w0. asatis M w0 (cDIAM m0 fl) \<and>
 (\<forall>l. length l \<noteq> length fl \<longrightarrow> \<not> asatis M w0 (cDIAM m' l))\<close> by blast
qed


lemma cDIAM_fl_length_cong0:
  assumes sat:"\<And>i. i < length fl \<Longrightarrow> asatis (Ms i) ((ws i)::'a) (fl ! i)"
  and "infinite (UNIV::'a set)"
  and "length l \<noteq> length fl"
shows "\<not>cequiv TYPE('a) (cDIAM m fl) (cDIAM m' l)"
  using all_asatis_cDIAM_asatis' 
  by (smt (verit, best) assms(2) assms(3) cequiv_def sat)


lemma cDIAM_fl_length_cong:
  assumes sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  and "infinite (UNIV::'a set)"
  and "length l \<noteq> length fl"
shows "\<not>cequiv TYPE('a) (cDIAM m fl) (cDIAM m' l)"
 by (metis assms(2) assms(3) cDIAM_fl_length_cong0 fl_satisfiable_exists_family sat)

lemma infinite_csatis_fl_cong:
  assumes "infinite (UNIV:: 'a set)"
  and "cequiv TYPE('a) (cDIAM m0 fl) (cDIAM m0 gl)"
shows 
   "(length fl = length gl \<and> 
  (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
   cequiv TYPE('a) (cDIAM m0 fl) cFALSE "
proof - 
  {assume sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
    then have ?thesis 
      by (metis assms(1) assms(2) cDIAM_fl_length_cong infinite_csatis_fl_cong_eq_length)
  }
  {assume "\<exists>f. f \<in> set fl \<and> (\<forall>M w::'a. \<not>  asatis M w f)"
    then have "cequiv TYPE('a) (cDIAM m0 fl) cFALSE"
      using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  then show ?thesis 
    using \<open>(\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w. asatis M w f) \<Longrightarrow> length fl = length gl \<and>
 (\<forall>j<length fl. cequiv TYPE('a) (fl ! j) (gl ! j)) \<or> 
cequiv TYPE('a) (cDIAM m0 fl) cFALSE\<close> by blast
qed



lemma infinite_csatis_fl_cong_eq_length':
  assumes "infinite (UNIV:: 'a set)"
  and len:"length fl = length gl"
  and "cequiv TYPE('a) (cDIAM m0 fl) (cDIAM m0 gl)"
shows 
   "(\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)) \<or> 
   cequiv TYPE('a) (cDIAM m0 fl) cFALSE \<and>
   cequiv TYPE('a) (cDIAM m0 gl) cFALSE "
proof -
  {assume sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
  and sat':"\<And>g. g \<in> set gl \<Longrightarrow> \<exists>M w::'a. asatis M w g"
    then have  "\<And>j. j < length fl \<Longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)"
      using infinite_csatis_fl_cong_lemma
      by (metis assms(1) assms(3) len)
  }
  {assume
    sat:"\<exists>f. f \<in> set fl \<and> (\<forall>M w::'a. \<not>asatis M w f)"
    then have " cequiv TYPE('a) (cDIAM m0 fl) cFALSE"using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  {assume
    sat:"\<exists>f. f \<in> set gl \<and> (\<forall>M w::'a. \<not>asatis M w f)"
    then have " cequiv TYPE('a) (cDIAM m0 gl) cFALSE"using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  show ?thesis 
    by (metis \<open>\<And>j. \<lbrakk>\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w. asatis M w f; \<And>g. g \<in> set gl \<Longrightarrow> \<exists>M w. asatis M w g;

  j < length fl\<rbrakk> \<Longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)\<close> 
\<open>\<exists>f. f \<in> set fl \<and> (\<forall>M w. \<not> asatis M w f) \<Longrightarrow>
 cequiv TYPE('a) (cDIAM m0 fl) cFALSE\<close> \<open>\<exists>f. f \<in> set gl \<and>
 (\<forall>M w. \<not> asatis M w f) \<Longrightarrow> cequiv TYPE('a) (cDIAM m0 gl) cFALSE\<close>
 asatis.simps(1) assms(3) cequiv_def)
qed


lemma infinite_csatis_fl_cong':
  assumes "infinite (UNIV:: 'a set)"
  and "cequiv TYPE('a) (cDIAM m0 fl) (cDIAM m0 gl)"
shows 
   "(length fl = length gl \<and> 
  (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
   (cequiv TYPE('a) (cDIAM m0 fl) cFALSE \<and>
    cequiv TYPE('a) (cDIAM m0 gl) cFALSE)"
proof - 
  {assume sat:"\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w::'a. asatis M w f"
    then have ?thesis 
      by (metis assms(1) assms(2) cDIAM_fl_length_cong infinite_csatis_fl_cong_eq_length')
  }
  {assume "\<exists>f. f \<in> set fl \<and> (\<forall>M w::'a. \<not>  asatis M w f)"
    then have "cequiv TYPE('a) (cDIAM m0 fl) cFALSE"
      using list_satis_not_exist_cDIAM_FALSE
    by metis
}
  then show ?thesis 
    using \<open>(\<And>f. f \<in> set fl \<Longrightarrow> \<exists>M w. asatis M w f) \<Longrightarrow> length fl = length gl \<and>
 (\<forall>j<length fl. cequiv TYPE('a) (fl ! j) (gl ! j)) \<or> 
(cequiv TYPE('a) (cDIAM m0 fl) cFALSE \<and>
 cequiv TYPE('a) (cDIAM m0 gl) cFALSE)\<close> 
    by (smt (verit, best) assms(2) cequiv_def)
qed

lemma  infinite_cDIAM_cong:
 assumes "infinite (UNIV:: 'a set)"
  and "cequiv TYPE('a) (cDIAM m1 fl) (cDIAM m2 gl)"
shows "(m1 = m2 \<and> 
      length fl = length gl \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
      cequiv TYPE('a) (cDIAM m1 fl) cFALSE"
  using  cDIAM_cequiv_cases infinite_csatis_fl_cong 
  by (metis assms(1) assms(2))


lemma cDIAM_cequiv_cases':
  assumes "infinite (UNIV::'a set)"
  and "cequiv TYPE('a) (cDIAM m1 fl1) (cDIAM m2 fl2)"
shows "(cequiv TYPE('a) (cDIAM m1 fl1) cFALSE \<and> cequiv TYPE('a) (cDIAM m2 fl2) cFALSE) \<or> m1 = m2"
proof -
  consider 
  (c1) "\<And>f. f \<in> set fl1 \<Longrightarrow> \<exists>M w::'a. asatis M w f" |
  (c2) "\<exists>f. f \<in> set fl1 \<and> (\<forall>M w::'a. \<not>asatis M w f)" 
    by blast
  then show ?thesis proof cases
    case c1
    then show ?thesis using infinite_cDIAM_cequiv_ops_eq 
     fl_satisfiable_exists_family
      by (metis assms(1) assms(2))
  next
    case c2
    then show ?thesis using list_satis_not_exist_cDIAM_FALSE cequiv_def
     by (metis assms(2))
  qed
qed

lemma  infinite_cDIAM_cong_iff_D1:
 assumes "infinite (UNIV:: 'a set)"
  and "cequiv TYPE('a) (cDIAM m1 fl) (cDIAM m2 gl)"
shows "(m1 = m2 \<and> 
      length fl = length gl \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
      (cequiv TYPE('a) (cDIAM m1 fl) cFALSE \<and> 
       cequiv TYPE('a) (cDIAM m2 gl) cFALSE)"
  using  cDIAM_cequiv_cases' infinite_csatis_fl_cong' 
  by (metis assms(1) assms(2))



lemma infinite_cDIAM_cong_iff_D2:
  assumes "(m1 = m2 \<and> 
      length fl = length gl \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
      (cequiv TYPE('a) (cDIAM m1 fl) cFALSE \<and> 
       cequiv TYPE('a) (cDIAM m2 gl) cFALSE)"
shows "cequiv TYPE('a) (cDIAM m1 fl) (cDIAM m2 gl)"
proof - 
  consider (c1) "(m1 = m2 \<and> 
      length fl = length gl \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j)))" |
     (c2) "cequiv TYPE('a) (cDIAM m1 fl) cFALSE \<and> 
       cequiv TYPE('a) (cDIAM m2 gl) cFALSE" using assms
    by fastforce
  then show ?thesis proof (cases)
    case c1
    then show ?thesis unfolding cequiv_def asatis.simps
      by (smt (verit, ccfv_SIG) fst_conv in_set_zip snd_conv)
  next
    case c2
    then show ?thesis
      by (meson cequiv_def)
  qed
qed


lemma infinite_cDIAM_cong_iff:
  assumes "infinite (UNIV::'a set)"
  shows "cequiv TYPE('a) (cDIAM m1 fl) (cDIAM m2 gl) \<longleftrightarrow>  (m1 = m2 \<and> 
      length fl = length gl \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (gl ! j))) \<or> 
      (cequiv TYPE('a) (cDIAM m1 fl) cFALSE \<and> 
       cequiv TYPE('a) (cDIAM m2 gl) cFALSE)"
  using infinite_cDIAM_cong_iff_D1 infinite_cDIAM_cong_iff_D2 
   by (metis assms)

end