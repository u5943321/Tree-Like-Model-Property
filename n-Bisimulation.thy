(* Title:        Part of the Modal Model Theory project
 * Content: Define and prove the basics for n-bisimulation
 *)
theory "n-Bisimulation"
  imports Main Modal_Syntax Modal_Model Modal_Semantics 
          Bounded_Morphism Generated_Submodel
begin

(*definition of n-bisimulation, Blackburn_prop2_31
 lemma 2.33 (about the n-bisimulation from a struct obtained 
 by restricting to some height and the original struct)
 is in Finite_Model*)

definition n_bisim :: 
 "(nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 
  ('m,'p,'a) struct \<Rightarrow> ('m,'p,'b) struct \<Rightarrow> 
  'a \<Rightarrow> 'b \<Rightarrow> bool" where
 "n_bisim Z n M M' w w' \<equiv>
  (\<forall>i v v'. Z i v v' \<longrightarrow> v \<in> world M \<and> v' \<in> world M') \<and>
  (\<forall>i v v'. i + 1 \<le> n --> Z (i + 1) v v' \<longrightarrow> Z i v v') \<and>
  (\<forall>v v' p. Z 0 v v' \<longrightarrow> valt M p v = valt M' p v') \<and>
  (\<forall>i v v' ul m. 
    i + 1 \<le> n \<and> Z (i + 1) v v' \<and> rel M m (v # ul) \<longrightarrow>
    (\<exists>ul'. 
      rel M' m (v' # ul') \<and> 
      (\<forall>u u'. (u,u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))) \<and>
  (\<forall>i v v' ul' m. 
    i + 1 \<le> n \<and> Z (i + 1) v v' \<and> rel M' m (v' # ul') \<longrightarrow>
    (\<exists>ul. 
      rel M m (v # ul) \<and> 
      (\<forall>u u'. (u,u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))) \<and> 
  Z n w w'
  "

lemma n_bisim_in_world:
  assumes "n_bisim Z n M M' w w'"
  shows "w \<in> world M" and "w' \<in> world M'" 
  apply (smt (verit) assms n_bisim_def) 
  by (smt (verit) assms n_bisim_def)


lemma n_bisim_chain :
  assumes nbs: "n_bisim Z n M M' w w'" 
  and j: "j \<le> n" 
  and i: "i \<le> j"
shows "Z j v v' \<longrightarrow> Z i v v'" using assms
 
proof - (*(induction n arbitrary: i j Z)*)
  define d where "d = j - i"
  show ?thesis using d_def i j
  proof (induction d arbitrary: i j)
    case 0 then have "i = j" by simp
    then show ?case by simp
  next
    case (Suc d)
    then have d: "d = j - (i + 1)"  
      using Suc.prems(1) by linarith
    then have "i + 1 \<noteq> j \<Longrightarrow> i + 1 \<le> j" using Suc by simp
    then consider 
    (c1) "i + 1 \<le> j" | (c2) "i + 1 = j" by blast
    then show ?case using Suc
    proof cases
      case c1 then 
      show " Z j v v' \<longrightarrow> Z i v v'" using Suc d
      proof (intro impI)
        assume "Z j v v'" then have "Z (i + 1) v v'" 
          using Suc.IH Suc.prems(3) c1 d by blast
        then show "Z i v v'" 
          using  j c1 nbs[unfolded n_bisim_def,THEN conjunct2,THEN conjunct1] 
          using Suc.prems(3) dual_order.trans by blast
      qed
    next 
      case c2 then 
      show " Z j v v' \<longrightarrow> Z i v v'" 
        using Suc nbs[unfolded n_bisim_def,THEN conjunct2, THEN conjunct1] 
        by blast
    qed
qed
qed


lemma n_bisim_0: 
  assumes nbs: "n_bisim Z n M M' w w'"
  shows "Z 0 w w'"
  using nbs[unfolded n_bisim_def,THEN conjunct2, THEN conjunct2, THEN conjunct2,
            THEN conjunct2,THEN conjunct2] nbs n_bisim_chain 
  by (metis bot_nat_0.extremum nat_le_linear)


lemma Blackburn_prop2_31_L2R_base:
assumes M: "is_struct sig M"
      and M': "is_struct sig M'"
      and nbs: "n_bisim Z n M M' w w'"
      and phi: "deg phi = 0"
    shows "csatis sig M w phi \<equiv> csatis sig M' w' phi"
  using phi
proof (induction phi )
  case (cVAR x) 
  show ?case 
    using nbs[unfolded n_bisim_def, THEN conjunct2,THEN conjunct2,
              THEN conjunct1] 
    unfolding csatis.simps nbs n_bisim_0
    by (metis n_bisim_0 n_bisim_in_world(1) n_bisim_in_world(2) nbs) 
next
  case cFALSE
  then show ?case by simp
next
  case (cDISJ phi1 phi2)
  then have phi1: "deg phi1 = 0" by simp
  from cDISJ have phi2: "deg phi2 = 0" by simp
  then show ?case using cDISJ.hyps(1) cDISJ.hyps(2) phi1 csatis.simps(3) 
    by simp
next
  case (cNOT phi)
  then have phi: "deg phi = 0" by simp
  then show ?case using cNOT.hyps(1) csatis.simps(4) 
    by (metis n_bisim_in_world(1) n_bisim_in_world(2) nbs)
next
  case (cDIAM x1a x2)
  have "False" using cDIAM.hyps(2) using deg.simps(5)
    by (metis add_is_0 zero_neq_one)
  then show ?case by simp
qed


lemma n_bisim_Z_world1 : 
  assumes nbs: "n_bisim Z n M M' w w'"
     and Z:"Z i v v'" shows "v \<in> world M" 
  using nbs[unfolded n_bisim_def, THEN conjunct1] Z by simp


lemma n_bisim_Z_world2 : 
  assumes nbs: "n_bisim Z n M M' w w'"
     and Z:"Z i v v'" shows "v' \<in> world M'" 
  using nbs[unfolded n_bisim_def, THEN conjunct1] Z by simp

lemma n_bisim_valt:
  assumes nbs: "n_bisim Z n M M' w w'"
     and i:"i \<le> n"
     and Z:"Z i v v'" shows "valt M p v = valt M' p v'"
proof -
  from assms have "Z 0 v v'" using n_bisim_chain[OF nbs] by blast
  then show ?thesis 
    using nbs[unfolded n_bisim_def, THEN conjunct2, THEN conjunct2,
              THEN conjunct1] by blast
qed


lemma n_bisim_below: 
 assumes M: "is_struct sig M"
      and M': "is_struct sig M'"
      and nbs: "n_bisim Z n M M' w w'"
      and k: "k \<le> n"
    shows "n_bisim Z k M M' w w'" unfolding n_bisim_def
proof (intro conjI impI allI)
  show "\<And>i v v'. Z i v v' \<Longrightarrow> v \<in> world M" using nbs[unfolded n_bisim_def]
    by metis
  show "\<And>i v v'. Z i v v' \<Longrightarrow> v' \<in> world M'" using nbs[unfolded n_bisim_def]
    by metis
  show "\<And>i v v'. i + 1 \<le> k \<Longrightarrow> Z (i + 1) v v' \<Longrightarrow> Z i v v'"
    using nbs[unfolded n_bisim_def] k 
    by (meson le_trans)
  show "\<And>v v' p. Z 0 v v' \<Longrightarrow> valt M p v = valt M' p v'"
    using nbs[unfolded n_bisim_def]
    by metis
  show "\<And>i v v' ul m.
       i + 1 \<le> k \<and> Z (i + 1) v v' \<and> rel M m (v # ul) \<Longrightarrow>
   \<exists>ul'. rel M' m (v' # ul') \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')"
     using nbs[unfolded n_bisim_def] k 
     by (meson le_trans)
  show "\<And>i v v' ul' m.
       i + 1 \<le> k \<and>
       Z (i + 1) v v' \<and> rel M' m (v' # ul') \<Longrightarrow>
       \<exists>ul. rel M m (v # ul) \<and>
            (\<forall>u u'.
                (u, u') \<in> set (zip ul ul') \<longrightarrow>
                Z i u u')"
     using nbs[unfolded n_bisim_def] k 
     by (meson le_trans)
   show "Z k w w'" using n_bisim_chain n_bisim_def nbs k nle_le 
     by (smt (verit))
 qed



lemma n_bisim_forward:
  assumes "n_bisim Z n M M' w w'"
  shows "\<And>i v v' ul m.
      i + 1 \<le> n \<Longrightarrow>
      Z (i + 1) v v' \<Longrightarrow> rel M m (v # ul) \<Longrightarrow>
      (\<exists>ul'. rel M' m (v' # ul') \<and>
             (\<forall>u u'.
                 (u, u') \<in> set (zip ul ul') \<longrightarrow>
                 Z i u u'))" 
  using assms[unfolded n_bisim_def,THEN conjunct2,THEN conjunct2,THEN conjunct2,
        THEN conjunct1] 
  by blast


lemma n_bisim_backward:
  assumes "n_bisim Z n M M' w w'"
  shows "\<And>i v v' ul' m. 
    i + 1 \<le> n \<Longrightarrow> Z (i + 1) v v' \<Longrightarrow> rel M' m (v' # ul') \<Longrightarrow>
    (\<exists>ul. 
      rel M m (v # ul) \<and> 
      (\<forall>u u'. (u,u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))" 
  using assms[unfolded n_bisim_def,THEN conjunct2,THEN conjunct2,THEN conjunct2,
        THEN conjunct2] 
  by blast

lemma n_bisim_below_n_bisim:
 assumes M: "is_struct sig M"
      and M': "is_struct sig M'"
      and nbs: "n_bisim Z n M M' w w'" 
      and i: "i \<le> n"
      and vv': "Z i v v'"
    shows "n_bisim Z i M M' v v'"
proof (unfold n_bisim_def, intro conjI allI impI)
  show "\<And>i v v'. Z i v v' \<Longrightarrow> v \<in> world M" using nbs[unfolded n_bisim_def] 
    by auto
  show "\<And>i v v'. Z i v v' \<Longrightarrow> v' \<in> world M'" using nbs[unfolded n_bisim_def] 
    by auto
  show "\<And>ia v v'. ia + 1 \<le> i \<Longrightarrow> Z (ia + 1) v v' \<Longrightarrow> Z ia v v'"
    using nbs[unfolded n_bisim_def] i
    by auto
  show "\<And>v v' p. Z 0 v v' \<Longrightarrow> valt M p v = valt M' p v'" using nbs[unfolded n_bisim_def] 
    by auto
  show "\<And>ia v v' ul m.
       ia + 1 \<le> i \<and> Z (ia + 1) v v' \<and> rel M m (v # ul) \<Longrightarrow>
       \<exists>ul'. rel M' m (v' # ul') \<and>
             (\<forall>u u'.
                 (u, u') \<in> set (zip ul ul') \<longrightarrow> Z ia u u')"
   using nbs[unfolded n_bisim_def] i
   by auto
  show "\<And>ia v v' ul' m.
       ia + 1 \<le> i \<and>
       Z (ia + 1) v v' \<and> rel M' m (v' # ul') \<Longrightarrow>
       \<exists>ul. rel M m (v # ul) \<and>
            (\<forall>u u'.
                (u, u') \<in> set (zip ul ul') \<longrightarrow>
                Z ia u u')"
   using nbs[unfolded n_bisim_def] i
   by (meson le_trans)
  show "Z i v v'" using vv'.
qed

lemma suc_n_bisim_rel:
  assumes M: "is_struct sig M"
      and M': "is_struct sig M'"
      and nbs: "n_bisim Z  (n + 1)  M M' w w'" 
      and wvl: "rel M m (w#vl)"
    shows "\<exists>vl'. rel M' m (w'#vl') \<and> 
                 (\<forall>v v'. (v,v') \<in> set (zip vl vl') \<longrightarrow> n_bisim Z n M M' v v')"
proof -
  from nbs have ww':"Z (n + 1) w w'" 
  by (simp add: n_bisim_def)
  from n_bisim_forward[OF nbs _ _ wvl]
  obtain ul' 
  where "rel M' m (w' # ul')" 
    and "\<And>u u'. (u, u') \<in> set (zip vl ul') \<Longrightarrow> Z n u u'" 
    using wvl ww' by blast
  then show ?thesis using n_bisim_below_n_bisim nbs 
    by (metis M M' le_add1)
qed



lemma Blackburn_prop2_31_L2R : 
  assumes M: "is_struct sig M"
      and M': "is_struct sig M'"
      and nbs: "n_bisim Z n M M' w w'"
      and phi: "deg phi \<le> n"
    shows "csatis sig M w phi \<equiv> csatis sig M' w' phi"
  using phi nbs
proof (induction n arbitrary : phi w w' Z)
  case 0
  then have d:"deg phi = 0" by simp 
  show ?case using  Blackburn_prop2_31_L2R_base[OF M M' 0(2) d] by simp 
next
  case (Suc n)
  show ?case using Suc
  proof (induction phi arbitrary : w w' rule: cform.induct)
    case (cVAR x)
    then have nbsn: "n_bisim Z n M M' w w' " using n_bisim_below[OF M M' cVAR(3),of n]
      by simp
    have d:"deg (cVAR x) \<le> n" by simp
    show ?case using Suc(1)[OF d nbsn]. 
  next
    case cFALSE
    then show ?case by auto
  next
    case (cDISJ x1a x2)
    then show ?case unfolding deg.simps csatis_simps 
      by force
  next
    case (cNOT x)
    then show ?case unfolding deg.simps csatis_simps csatis_in_world
     by (simp add: n_bisim_in_world(1) n_bisim_in_world(2))
  next
    case (cDIAM m fl)
    then have ww':"Z (n + 1) w w'" 
      by (smt (verit) Suc_eq_plus1 n_bisim_def)
    have f:"\<And>f. f \<in> set fl \<Longrightarrow> deg f \<le> n" using deg_cDIAM_bound 
      by (metis Suc_eq_plus1 cDIAM.prems(2))
    from cDIAM show ?case
    proof (intro iffI)
      assume LHS: "csatis sig M w (cDIAM m fl)" 
      then have mo:"m \<in> ops sig" 
           and ma:"arity sig m = length fl" 
           and w:" w \<in> world M" unfolding csatis_simps5[OF M]
      
      proof - qed simp_all
      
      from LHS obtain vl where
      len:"length vl = length fl"
      and wvl:"rel M m (w # vl)"
      and sz:"\<And>x y. (x, y) \<in> set (zip vl fl) \<Longrightarrow>
               csatis sig M x y" 
        by auto

      then show "csatis sig M' w' (cDIAM m fl)" unfolding csatis_simps5[OF M']
      proof (intro conjI)
        show "m \<in> ops sig" using mo.
        show "arity sig m = length fl" using ma.
        show "w' \<in> world M'" using n_bisim_in_world[OF cDIAM(4)] by simp
        from n_bisim_forward[OF cDIAM(4) _ ww' wvl]
        obtain ul' where
        w'ul': "rel M' m (w' # ul')" and
        uu':"\<And>u u'. (u, u') \<in> set (zip vl ul') \<Longrightarrow> Z n u u'" by auto
        from w'ul' mo ma M M' len wvl is_struct_rel_same_length 
        have lenul':"length ul' = length vl" 
          by (metis length_Cons nat.inject)
        with uu' n_bisim_below_n_bisim[OF M M' cDIAM(4), of n] have 
        uu'nbs: "\<And>u u'. (u, u') \<in> set (zip vl ul') \<Longrightarrow> n_bisim Z n M M' u u'"
          using le_Suc_eq by blast
        with cDIAM(2) f have 
        eqsts:"\<And>u u' f. (u, u') \<in> set (zip vl ul') \<Longrightarrow> f \<in> set fl \<Longrightarrow>
        csatis sig M u f = csatis sig M' u' f" by blast
        with sz have "(\<forall>x y. (x, y) \<in> set (zip ul' fl) \<longrightarrow>
                csatis sig M' x y)" 
        proof (intro allI impI)
          fix u' f
          assume u'f:"(u', f) \<in> set (zip ul' fl)"
          then obtain k
            where "k < length fl" 
            and ul'k: "u' = ul' ! k" 
            and flk: "f = fl ! k" 
            by (metis in_set_zip prod.sel(1) prod.sel(2))
          then have vf: "(vl ! k, f) \<in> set (zip vl fl)"
            using len lenul' in_set_zip by force
          have vu': "(vl ! k,u') \<in> set (zip vl ul')" 
            using \<open>k < length fl\<close> in_set_zip len lenul' ul'k
            by fastforce
          then show "csatis sig M' u' f" 
            using eqsts sz[OF vf] u'f 
            by (meson set_zip_rightD)
        qed
        then 
        
        have "\<exists>vl. length vl = length fl \<and>
         rel M' m (w' # vl) \<and>
         (\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow>
                csatis sig M' x y) " using w'ul' len lenul' 
          by auto
        then show
        "\<exists>vl. length vl = length fl \<and>
         rel M' m (w' # vl) \<and>
         (\<forall>i<length vl.
             csatis sig M' (vl ! i)
              (fl ! i))" 
          by (metis fst_conv in_set_zip snd_conv)
      qed
    next 
      assume RHS: "csatis sig M' w' (cDIAM m fl)" 
      then have mo:"m \<in> ops sig" 
           and ma:"arity sig m = length fl" 
           and w:" w' \<in> world M'" 
        unfolding csatis_simps5[OF M'] proof - qed simp_all
      from RHS obtain vl' where 
      len:"length vl' = length fl"
      and w'vl':"rel M' m (w' # vl')"
      and sz:"\<And>x y. (x, y) \<in> set (zip vl' fl) \<Longrightarrow>
               csatis sig M' x y" 
        by auto
      then show "csatis sig M w (cDIAM m fl)" unfolding csatis_simps5[OF M]
      proof (intro conjI)
        show "m \<in> ops sig" using mo.
        show "arity sig m = length fl" using ma.
        show "w \<in> world M" using n_bisim_in_world[OF cDIAM(4)] by simp
        from n_bisim_backward[OF cDIAM(4) _ ww' w'vl']
        obtain vl where
        wvl: "rel M m (w # vl)" and
        vv':"\<And>v v'. (v, v') \<in> set (zip vl vl') \<Longrightarrow> Z n v v'"
          by auto
        from w'vl' mo ma M M' len wvl is_struct_rel_same_length 
        have lenul':"length vl' = length vl" 
          by (metis length_Cons nat.inject)
         
        with vv' n_bisim_below_n_bisim[OF M M' cDIAM(4), of n] have 
        vv'nbs: "\<And>v v'. (v, v') \<in> set (zip vl vl') \<Longrightarrow> 
                  n_bisim Z n M M' v v'"
          using le_Suc_eq by blast
        with cDIAM(2) f have 
        eqsts:"\<And>u u' f. (u, u') \<in> set (zip vl vl') \<Longrightarrow> f \<in> set fl \<Longrightarrow>
        csatis sig M u f = csatis sig M' u' f" by blast
        with sz have "\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow>
                csatis sig M x y" 
        proof (intro allI impI)
          fix v f
          assume vf:"(v, f) \<in> set (zip vl fl)"
          then obtain k
            where "k < length fl" 
            and vlk: "v = vl ! k" 
            and flk: "f = fl ! k" 
            by (metis in_set_zip prod.sel(1) prod.sel(2))
          then have vf: "(vl' ! k, f) \<in> set (zip vl' fl)"
            using len lenul' in_set_zip by force
          have vu': "(v,vl' ! k) \<in> set (zip vl vl')" 
            using \<open>k < length fl\<close> in_set_zip len lenul' vlk
            by fastforce
          then show "csatis sig M v f" 
            using eqsts sz[OF vf] vf 
            by (meson set_zip_rightD)
        qed
        then have "\<exists>vl. length vl = length fl \<and>
         rel M m (w # vl) \<and>
         (\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow>
                csatis sig M x y) " using wvl len lenul' 
          by auto
        then show 
         "(\<exists>vl. length vl = length fl \<and>
          rel M m (w # vl) \<and>
          (\<forall>i<length vl.
              csatis sig M (vl ! i)
               (fl ! i)))" 
          by (metis fst_conv in_set_zip snd_conv)
      qed
  qed
qed  
qed


end