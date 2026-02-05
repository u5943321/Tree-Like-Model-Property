(* Title:        Part of the Modal Model Theory project
 * Content:      Upgrade the HOL version of finite model property using ZF.
                 The whole aim is to hide the type parameter.
 *)




theory FMP_in_HOLZF
imports Main Modal_Syntax Modal_Model Modal_Semantics 
          Bounded_Morphism Generated_Submodel "n-Bisimulation"
           Tree_Like_Model "deg_wffs" Finite_Model Upgraded_TLP_and_FMP
         ZFC_in_HOL.ZFC_in_HOL

begin


definition Vstruct2struct where
 "Vstruct2struct M \<equiv> (elts (fst M),(fst (snd M)),snd (snd M))"

definition is_Vstruct where
 "is_Vstruct sig M \<equiv> is_struct sig (Vstruct2struct M)"



definition Vsatis where
"Vsatis M w phi \<equiv> asatis (Vstruct2struct M) w phi"



abbreviation Vworld where
"Vworld M \<equiv> elts (fst M)"


abbreviation Vrel where
"Vrel M \<equiv> fst (snd M)"

lemma small_alt: "small A \<longleftrightarrow> (\<exists>B :: V. |A| =o |elts B| )"
  unfolding small_def card_of_ordIso[symmetric] bij_betw_def
  by auto

lemma small_lists:
  assumes "small A"
  shows "small (lists A)"
proof (cases "countable A")
  case True
  then show ?thesis 
    by (simp add: countable)
next
  case False
  then show ?thesis  
    by (meson assms card_of_lists_infinite ordIso_transitive small_alt uncountable_infinite)
qed
 
definition im_rel where 
"im_rel i R \<equiv> {p. (\<exists> r1 r2. (r1,r2) \<in> R \<and> p = (i r1, i r2))}"

theorem im_rel_trancl_preimage:
  assumes "(x,y) \<in> (im_rel i R)\<^sup>+"
  shows "x \<in> i ` (Domain R) \<and> y \<in> i ` (Range R)" using assms
proof (induction)
  case (base y)
  then show ?case 
    by (smt (verit, ccfv_threshold) Domain.DomainI Pair_inject 
Range.intros im_rel_def image_iff mem_Collect_eq) 
next
  case (step y z)
  then show ?case 
    by (smt (verit, ccfv_SIG) Range.intros im_rel_def image_eqI mem_Collect_eq snd_conv) 
qed


theorem im_rel_trancl_preimage':
  assumes i:"inj_on i (Domain R \<union> Range R)"
  assumes xy:"(x,y) \<in> (im_rel i R)\<^sup>+"
  shows "\<exists>x0 y0. x0 \<in> (Domain R) \<and> y0 \<in>  (Range R) \<and> x = i x0 \<and> y = i y0 \<and> (x0,y0) \<in> R\<^sup>+" using xy
proof (induction)
  case (base y)
  then show ?case 
    by (smt (verit) Domain.DomainI Pair_inject Range.intros im_rel_def 
   mem_Collect_eq trancl.r_into_trancl)
next
  case (step y z)
  then obtain x0 y0 where
  " x0 \<in> Domain R \<and>
       y0 \<in> Range R \<and>
       x = i x0 \<and> y = i y0 \<and> (x0, y0) \<in> R\<^sup>+" by blast
  obtain z0 where "(y0,z0) \<in> R  \<and> i z0 = z" using i im_rel_def
    by (smt (verit, best) CollectD FieldI1 FieldI2 Field_def Pair_inject \<open>x0 \<in> Domain R \<and>
    y0 \<in> Range R \<and> x = i x0 \<and> y = i y0 \<and> (x0, y0) \<in> R\<^sup>+\<close> inj_onD step.hyps(2) 
   trancl_domain trancl_range)
  
  then show ?case
    by (metis (no_types, opaque_lifting) Range.simps Transitive_Closure.trancl_into_trancl 
   \<open>x0 \<in> Domain R \<and> y0 \<in> Range R \<and> x = i x0 \<and> y = i y0 \<and> (x0, y0) \<in> R\<^sup>+\<close>)
qed

theorem trancl_inj:
  assumes "inj_on i (Domain R \<union> Range R)"
  shows " im_rel i (R\<^sup>+) = (im_rel i R)\<^sup>+" using assms
proof -
  { fix ix iy
    assume a:"(ix,iy) \<in> im_rel i (R\<^sup>+)"
    then obtain x y where xy:"(x,y)\<in> R\<^sup>+" and "i x = ix" and "i y = iy"
      unfolding im_rel_def by blast
    from xy have "(i x,i y) \<in> (im_rel i R)\<^sup>+"
    proof (rule trancl.induct)
      show 
      "\<And>a b. (a, b) \<in> R \<Longrightarrow>
           (i a, i b) \<in> (im_rel i R)\<^sup>+" 
        using im_rel_def by fastforce
      show 
      "\<And>a b c.
       (a, b) \<in> R\<^sup>+ \<Longrightarrow>
       (i a, i b) \<in> (im_rel i R)\<^sup>+ \<Longrightarrow>
       (b, c) \<in> R \<Longrightarrow>
       (i a, i c) \<in> (im_rel i R)\<^sup>+"
        by (meson \<open>\<And>b a. (a, b) \<in> R \<Longrightarrow> (i a, i b) \<in> (im_rel i R)\<^sup>+\<close> trancl_trans)
     
    qed
    then have "(ix,iy) \<in> (im_rel i R)\<^sup>+" 
      using \<open>i x = ix\<close> \<open>i y = iy\<close> by blast
  }
  
  {fix x1 y1 assume "(x1,y1) \<in> (im_rel i R)\<^sup>+"
    then have " (x1,y1) \<in> im_rel i (R\<^sup>+)"
      using im_rel_trancl_preimage'
      using assms im_rel_def by fastforce
  }
  then show ?thesis using subsetI 
    by (meson \<open>\<And>iy ix. (ix, iy) \<in> im_rel i (R\<^sup>+) \<Longrightarrow> (ix, iy) \<in> (im_rel i R)\<^sup>+\<close> pred_equals_eq2)
qed


theorem rtrancl_inj:
  assumes "inj_on i (Domain R \<union> Range R)"
  shows " im_rel i (R\<^sup>*) \<subseteq> (im_rel i R)\<^sup>*" using assms
proof -
  {fix x y 
    assume "(x,y) \<in> im_rel i (R\<^sup>*)"
    then obtain x0 y0 where x:"x = i x0" and y:"y = i y0"  and x0y0: "(x0,y0) \<in> R\<^sup>*"
      using im_rel_def 
      by (smt (verit, del_insts) CollectD Pair_inject)
    from x0y0 have "(i x0,i y0) \<in> (im_rel i R)\<^sup>*"
    proof (induction)
      case base
      then show ?case by blast
    next
      case (step y z)
      then show ?case 
        by (metis (mono_tags, lifting) im_rel_def mem_Collect_eq rtrancl.rtrancl_into_rtrancl)
    qed
    then have "(x,y) \<in> (im_rel i R)\<^sup>*" 
      using x y by fastforce
  }
  then show ?thesis 
    using subrelI by blast
qed

definition im_mrel where
"im_mrel i R \<equiv>  \<lambda>m wl. if (\<exists>wl0.  map i wl0 =wl) 
    then (\<forall>wl0.  map i wl0 =wl \<longrightarrow> R m wl0) else False"

theorem Domain_U_Range_gen_birel:
  assumes ss0:"rset \<tau> R \<subseteq> W"
  shows "(Domain (gen_birel \<tau> R) \<union>
      Range (gen_birel \<tau> R)) \<subseteq> W"
proof - 
  {fix x assume "x \<in> Domain (gen_birel \<tau> R)"
    then obtain y where "(x,y) \<in> gen_birel \<tau> R"
      by blast
    then have "x \<in> W" using ss0 rset_def gen_birel_def
     by (simp add: gen_birel_rset1 subsetD) }
  {fix y assume "y \<in>  Range (gen_birel \<tau> R)"
    then obtain x where "(x,y) \<in> gen_birel \<tau> R"
      by blast
    then have "y \<in> W" using ss0 rset_def gen_birel_def
     by (simp add: gen_birel_rset2 subsetD)
    
 }
  then show ?thesis 
    by (simp add: \<open>\<And>x. x \<in> Domain (gen_birel \<tau> R) \<Longrightarrow> x \<in> W\<close> subsetI)
qed

theorem tree_inj_tree:
  assumes t:"tree \<tau> (W,R) r"
  and ss0:"rset \<tau> R \<subseteq> W"
  and i:"inj_on i W"
defines 
  "iR \<equiv> 
   \<lambda>m wl. if (\<exists>wl0. list.set wl0 \<subseteq> W \<and> map i wl0 =wl) 
    then (\<forall>wl0. list.set wl0 \<subseteq> W \<and>  map i wl0 =wl \<longrightarrow> R m wl0) else False"
shows "tree \<tau> (i ` W,iR) (i r)"
proof -
  have "i r \<in> i ` W" using i
    using assms(1) root_in_tree by fastforce
  have ss:"rset \<tau> iR \<subseteq> i ` W" unfolding iR_def rset_def
    by (smt (verit, best) CollectD image_mono list.set_map subsetD subsetI) 
  (* (\<forall>t. t \<in> i ` W \<longrightarrow>
         (i r, t) \<in> (gen_birel \<tau> iR)\<^sup>*)
  have gbi:"(gen_birel \<tau> iR) = im_rel i (gen_birel \<tau> R)" 
  proof -
    {fix x y assume "(x,y) \<in> gen_birel \<tau> iR"
      then obtain m ul where
      " m \<in> \<tau>" and  xul:"iR m (x # ul)" and y: "y \<in> list.set ul"
        unfolding gen_birel_def mem_Collect_eq by blast
      from xul obtain wl0 where
      wl0W:"list.set wl0 \<subseteq> W " and
      iwl0: "map i wl0 = x # ul" and
      " R m wl0" unfolding iR_def by meson
      from iwl0 obtain x0 ul0 where "wl0 = x0 # ul0"
      and "i x0 = x" and "map i ul0 = ul" by blast
      then obtain y0 where "y0 \<in> list.set ul0" and "i y0 = y"
        using y by fastforce
      then have "(x0,y0) \<in>gen_birel \<tau> R" 
        using \<open>R m wl0\<close> \<open>m \<in> \<tau>\<close> \<open>wl0 = x0 # ul0\<close> gen_birel_def by fastforce
      have "x0 \<in> W" using wl0W
        by (simp add: \<open>wl0 = x0 # ul0\<close>)
      have "y0 \<in> W" using wl0W 
        by (meson \<open>(x0, y0) \<in> gen_birel \<tau> R\<close> gen_birel_rset2 ss0 subsetD)
      have "(i x0,i y0) \<in> im_rel i (gen_birel \<tau> R)"
        using \<open>(x0, y0) \<in> gen_birel \<tau> R\<close> im_rel_def by fastforce
      then have "(x,y) \<in> im_rel i (gen_birel \<tau> R)"
     
        using \<open>i x0 = x\<close> \<open>i y0 = y\<close> by blast
    }
    {fix x y assume xy:"(x,y) \<in> im_rel i (gen_birel \<tau> R)"
      then obtain x0 y0 where 
      x0y0:"(x0, y0) \<in> gen_birel \<tau> R" and 
      "(x, y) = (i x0, i y0)"
        unfolding im_rel_def mem_Collect_eq by blast
      from ss0 x0y0 have "x0 \<in> W" 
        by (simp add: gen_birel_rset1 in_mono)
      from ss0 x0y0 have "y0 \<in> W" 
        by (simp add: gen_birel_rset2 in_mono)
      from x0y0 obtain m ul where 
        "m \<in> \<tau>" and x0ul: "R m (x0 # ul)" and 
        "y0 \<in> list.set ul" 
        unfolding gen_birel_def mem_Collect_eq by blast
      then have "list.set (x0 # ul) \<subseteq> W" using ss0 
        using rset_def by fastforce
      then have "iR m (i x0 # map i ul)" unfolding iR_def
      x0ul 
        by (smt (verit, ccfv_threshold) i inj_on_contraD inj_on_image_eq_iff list.inj_map_strong 
        list.set_map list.simps(9) subset_inj_on x0ul)
      then have "(i x0, i y0) \<in> (gen_birel \<tau> iR)"
        using \<open>m \<in> \<tau>\<close> \<open>y0 \<in> list.set ul\<close> gen_birel_def by fastforce
      then have "(x,y) \<in> gen_birel \<tau> iR" 
        using \<open>(x, y) = (i x0, i y0)\<close> by blast
    }
    then show "(gen_birel \<tau> iR) = im_rel i (gen_birel \<tau> R)"
    using \<open>\<And>y x. (x, y) \<in> gen_birel \<tau> iR \<Longrightarrow> (x, y) \<in> im_rel i (gen_birel \<tau> R)\<close> by auto
  qed
    
  {fix t assume "t \<in> i ` W"
    then obtain t0 where t0:"t0 \<in> W" and it0:"i t0 = t"
      by blast
    from t[unfolded tree_ss_alt[OF ss0],THEN conjunct2] t0 have 
    "(r,t0) \<in> (gen_birel \<tau> R)\<^sup>*" by blast
    then have "(i r, i t0) \<in> im_rel i ((gen_birel \<tau> R)\<^sup>*)"
      using im_rel_def by fastforce
    then have "(i r, t) \<in> (gen_birel \<tau> iR)\<^sup>*" 
      using rtrancl_inj[of i "gen_birel \<tau> R"]
      by (smt (verit, best) Domain_U_Range_gen_birel \<open>(gen_birel \<tau> iR) = im_rel i (gen_birel \<tau> R)\<close>
         i inj_on_def it0 rtrancl_idemp ss0 subsetD)
  }
  {fix t assume "t \<in> i ` W" 
   then obtain t0 where t0:"t0 \<in> W" and it0:"i t0 = t"
     by blast
   then have "(t0,t0) \<notin> (gen_birel \<tau> R)\<^sup>+ "
     using t[unfolded tree_ss_alt[OF ss0],THEN conjunct2] t0
     by blast
   then have "(i t0, i t0) \<notin> im_rel i ((gen_birel \<tau> R)\<^sup>+)" 
     using im_rel_def  trancl_inj gbi 
     by (smt (verit, best) Domain_U_Range_gen_birel i im_rel_trancl_preimage' in_mono inj_onD 
      inj_on_subset ss0 sup.boundedE t0)
   then have "(t,t) \<notin> (gen_birel \<tau> iR)\<^sup>+" 
     by (metis Domain_U_Range_gen_birel gbi i inj_on_subset it0 ss0 trancl_inj)
 }
  {fix t assume "t \<in> i ` W" and "t \<noteq> i r"
   then obtain t0 where t0:"t0 \<in> W" and it0:"i t0 = t"
     by blast
   then have "t0 \<noteq> r" using i 
     using \<open>t \<noteq> i r\<close> by force
   then have
   "\<exists>! t0'. (t0',t0) \<in> gen_birel \<tau> R" 
   using t[unfolded tree_ss_alt[OF ss0],THEN conjunct2] t0
   by blast
  then obtain "t0'" where "(t0',t0) \<in> gen_birel \<tau> R" and
  "\<And>t0''. (t0'',t0) \<in> gen_birel \<tau> R \<Longrightarrow> t0'' = t0'" by metis
  then have " (i t0',i t0) \<in> gen_birel \<tau> iR"
    using gbi im_rel_def by blast
  have "\<And>it0''. (it0'',i t0) \<in> gen_birel \<tau> iR \<Longrightarrow> it0'' = i t0'"
    by (smt (verit) Pair_inject \<open>(t0', t0) \<in> gen_birel \<tau> R\<close> 
    \<open>\<And>t0''. (t0'', t0) \<in> gen_birel \<tau> R \<Longrightarrow> t0'' = t0'\<close> gbi gen_birel_rset2 i 
    im_rel_def inj_on_def inj_on_subset mem_Collect_eq ss0)
  then have "(\<exists>!t'. (t', t) \<in> gen_birel \<tau> iR)"
    using \<open>(i t0', i t0) \<in> gen_birel \<tau> iR\<close> it0 by blast
  }
  show ?thesis unfolding tree_ss_alt[OF ss] 
  
    using \<open>\<And>t. \<lbrakk>t \<in> i ` W; t \<noteq> i r\<rbrakk> \<Longrightarrow> \<exists>!t'. (t', t) \<in> gen_birel \<tau> iR\<close>
   \<open>\<And>t. t \<in> i ` W \<Longrightarrow> (i r, t) \<in> (gen_birel \<tau> iR)\<^sup>*\<close>
    \<open>\<And>t. t \<in> i ` W \<Longrightarrow> (t, t) \<notin> (gen_birel \<tau> iR)\<^sup>+\<close> 
   \<open>i r \<in> i ` W\<close> by blast
qed



definition inj_rel where 
"inj_rel i W R \<equiv> 
 \<lambda>m wl. if (\<exists>wl0. list.set wl0 \<subseteq> W \<and> map i wl0 =wl) 
    then (\<forall>wl0. list.set wl0 \<subseteq> W \<and>  map i wl0 =wl \<longrightarrow> R m wl0) else False"

definition inj_valt where 
"inj_valt i W V \<equiv> \<lambda>p v. if (\<exists>v0. v0 \<in> W \<and> i v0 = v) then
        (\<forall>v0. v0 \<in> W \<and> i v0 = v \<longrightarrow> V p v0) else False"

definition inj_struct where
"inj_struct i M \<equiv> 
 (i ` world M, inj_rel i (world M) (rel M), inj_valt i (world M) (valt M))"


lemma inj_asatis :
  assumes "inj_on i (world M)"
  and w:"w \<in> world M"
  shows "asatis M w f \<equiv> asatis (inj_struct i M) (i w) f" using w
proof (induction f arbitrary: w)
  case (cVAR x)
  then show ?case unfolding asatis.simps fst_conv snd_conv inj_struct_def
  inj_valt_def using inj_on_def 
   by (metis (mono_tags, lifting) assms(1) rev_image_eqI)
next
  case cFALSE
  then show ?case by simp
next
  case (cDISJ f1 f2)
  then show ?case   by auto
next
  case (cNOT f)
  then show ?case 
    by (simp add: inj_struct_def)
  
next
  case (cDIAM m fl)
  {assume lhs: "asatis M w (cDIAM m fl) "
    then obtain vl where 
   len : "length vl = length fl" and 
   rel : "rel M m (w # vl)" and 
   sat : "\<And>v f. (v,f) \<in> list.set (zip vl fl) \<Longrightarrow> asatis M v f"
      unfolding asatis.simps  by blast
    have "list.set (w # vl) \<subseteq> world M" 
      by (metis asatis_in_world cDIAM.hyps(2) in_set_impl_in_set_zip1 len sat set_ConsD subsetI)
    have "\<And>wvl'. list.set wvl' \<subseteq> world M \<and> map i wvl' = map i (w # vl) ==> wvl' =(w # vl)  "
   using  inj_on_def 
   by (meson \<open>list.set (w # vl) \<subseteq> world M\<close> assms(1) inj_on_map_eq_map le_sup_iff subset_inj_on)
    then have "rel (inj_struct i M) m (i w # map i vl) " unfolding inj_struct_def copy_rel_def
     
      by (smt (verit) \<open>list.set (w # vl) \<subseteq> world M\<close> fst_conv inj_rel_def list.simps(9)
      local.rel snd_conv)
    have wM: "w \<in> world M" using asatis_in_world 
      using cDIAM.hyps(2) by auto
    from sat asatis_in_world have vl_ss_M:"list.set vl \<subseteq> world M" 
      by (metis in_set_impl_in_set_zip1 len subsetI)
    {fix iv f assume "(iv, f) \<in> list.set (zip (map i vl) fl)" 
      (*critical thing is the (v,f) in the zip list*)
      obtain v where v:"v \<in> list.set vl" and "i v = iv" 
        by (metis \<open>(iv, f) \<in> list.set (zip (map i vl) fl)\<close> \<open>list.set vl \<subseteq> world M\<close> 
        imageE image_set set_zip_leftD)
      have f: "f \<in> list.set fl"
        by (metis \<open>(iv, f) \<in> list.set (zip (map i vl) fl)\<close> set_zip_rightD)
      from cDIAM(1)[OF f ] sat
      have "asatis (inj_struct i M) iv f" 
        by (metis \<open>(iv, f) \<in> list.set (zip (map i vl) fl)\<close> fst_conv 
       in_set_zip len nth_map nth_mem snd_conv subsetD vl_ss_M) }
    then have "asatis (inj_struct i M) (i w) (cDIAM m fl)" 
      by (smt (verit, best) \<open>Vrel (inj_struct i M) m (i w # map i vl)\<close> asatis.simps(5)
   fstI inj_struct_def len length_map rev_image_eqI wM)
      
  }
  {assume rhs: "asatis (inj_struct i M) (i w) (cDIAM m fl)" 
   then obtain ivl where 
   len : "length ivl = length fl" and 
   rel : "rel (inj_struct i M) m (i w # ivl)" and 
   sat : "\<And>iv f. (iv,f) \<in> list.set (zip ivl fl) \<Longrightarrow> asatis (inj_struct i M) iv f"
     unfolding asatis.simps by blast
   then obtain vl where 
   "ivl = map i vl" and "rel M m (w # vl)" and vl_ss_M:"list.set vl \<subseteq> world M" 
     unfolding inj_struct_def inj_rel_def using assms 
     using inj_onD 
     by (smt (verit, ccfv_SIG) cDIAM.hyps(2) fstI in_mono list.set_intros(1)
      map_eq_Cons_D set_subset_Cons sndI subset_trans)
    
    {fix v f assume "(v, f) \<in> list.set (zip vl fl)" 
      have f: "f \<in> list.set fl"
        by (metis \<open>(v, f) \<in> list.set (zip vl fl)\<close> set_zip_rightD)
      from cDIAM(1)[OF f] sat
      have "asatis M v f" 
        by (metis \<open>(v, f) \<in> list.set (zip vl fl)\<close> \<open>ivl = map i vl\<close> fst_conv in_set_zip len 
          nth_map set_zip_leftD snd_conv subsetD vl_ss_M)
       }
       then have "asatis M w (cDIAM m fl) " 
         using \<open>Vrel M m (w # vl)\<close> \<open>ivl = map i vl\<close> cDIAM.hyps(2) len by auto
       }
  then show ?case 
    using \<open>asatis M w (cDIAM m fl) \<Longrightarrow> asatis (inj_struct i M) (i w) (cDIAM m fl)\<close> by blast
qed


theorem Finite_Tree_Model_Property_V:
  assumes wff:"wff sig00 \<phi>"
  and "Vsatis M00 w00 \<phi>"
assumes "is_Vstruct sig00 M00"
defines "sig \<equiv> restrict_sig sig00 ( modal_operators \<phi>) (prop_letters \<phi>)"
shows 
  "\<exists>fM fw. is_Vstruct sig fM \<and>
           finite (Vworld fM) \<and> 
           tree (ops sig) (Vworld fM,Vrel fM) fw \<and> 
           Vsatis fM fw \<phi>"
proof - 
  have sat00:"asatis (Vstruct2struct M00) w00 \<phi>"
    using Vsatis_def assms(2) by blast
  have mod00:"is_struct sig00 (Vstruct2struct M00)" 
    using assms(3) is_Vstruct_def by blast
  from Finite_Tree_Model_Property[OF wff sat00 mod00]
  obtain fM fw where 
  is_struct_fM:"is_struct sig fM" and
   " world fM
     \<subseteq> {l. list.set l
            \<subseteq> world (Vstruct2struct M00)} " and
   fin_fM: "finite (world fM) " and
   " tree
      (ops (restrict_sig sig00
             (modal_operators \<phi>)
             (prop_letters \<phi>)))
      (world fM, rel fM) fw " and
     sat : "asatis fM fw \<phi>" using sig_def
    by blast
  have "small (Vworld M00)" by force
  then have "small (lists (Vworld M00))" using small_lists
    by metis
  have "world fM \<subseteq> (lists (Vworld M00))" 
    by (metis Vstruct2struct_def \<open>world fM \<subseteq> {l. list.set l \<subseteq> world (Vstruct2struct M00)}\<close> 
   lists_eq_set prod.sel(1))
   then have "small (world fM)"
    using \<open>small (lists (Vworld M00))\<close> smaller_than_small by auto
  then obtain i where
    inj_i: "inj_on i (world fM)" and
    "i ` world fM \<in> range elts"
     unfolding small_def
     by blast
   then obtain Wv where eWv:"elts Wv = i ` world fM" 
     by force
   define R where "R \<equiv> rel fM"
   define W where "W \<equiv> world fM"
   define V where "V \<equiv> valt fM"
   define iR where "iR \<equiv> \<lambda>m wl. if (\<exists>wl0. list.set wl0 \<subseteq> W \<and> map i wl0 =wl) 
    then (\<forall>wl0. list.set wl0 \<subseteq> W \<and>  map i wl0 =wl \<longrightarrow> R m wl0) else False"
   define iV where "iV \<equiv> \<lambda>p v. if (\<exists>v0. v0 \<in> W \<and> i v0 = v) then
        (\<forall>v0. v0 \<in> W \<and> i v0 = v \<longrightarrow> V p v0) else False"
   define iM where  "iM \<equiv> (Wv, iR, iV)"
   have "Vworld iM = i ` world fM" 
     by (simp add: \<open>elts Wv = i ` world fM\<close> iM_def)
   with inj_i fin_fM have "finite (Vworld iM)" by auto
   have tree_cond:" tree (ops sig) (W, R) fw"
     using R_def W_def \<open>tree (ops (restrict_sig sig00 (modal_operators \<phi>) (prop_letters \<phi>))) 
      (world fM, Vrel fM) fw\<close> sig_def by fastforce
   have rset_cond:"rset (ops sig) R \<subseteq> W" using  is_struct_rel_ss_world 
     using R_def W_def is_struct_fM by blast
   have 
   "tree (ops sig) (i ` W,iR) (i fw)"
     using tree_inj_tree[of "ops sig" W R fw i,OF tree_cond rset_cond] inj_i W_def
     unfolding iR_def by blast
   then have
   "tree (ops sig) (Vworld iM,Vrel iM) (i fw)" 
     using W_def \<open>Vworld iM = i ` world fM\<close> iM_def by auto
   have "i fw \<in> elts Wv" 
     using W_def \<open>tree (ops sig) (i ` W, iR) (i fw)\<close> eWv root_in_tree by fastforce
   have c1:"(\<forall>p w. iV p w \<longrightarrow>
           p \<in> props sig \<and> w \<in> elts Wv)"
     unfolding iV_def eWv W_def 
   proof -
     {fix p w assume 
      "\<exists>v0. v0 \<in> world fM \<and> i v0 = w"
       and 
      Vp: "\<forall>v0. v0 \<in> world fM \<and>
                     i v0 = w \<longrightarrow>
                     V p v0"
       then obtain v0 where 
      v0fM: "v0 \<in> world fM" and iv0: "i v0 = w" by blast
      then have "V p v0" using Vp by metis
      then have p:"p \<in> props sig" 
        using is_struct_fM
         unfolding V_def is_struct_def
         by blast
       from iv0 v0fM have "w \<in> elts Wv" unfolding eWv
         by blast
       with p have "p \<in> props sig \<and> w \<in> i ` world fM"
      using eWv by blast
     (*p \<in> props sig \<and> w \<in> i ` world fM*)
   }
   then show
    "\<forall>p w. (if \<exists>v0. v0 \<in> world fM \<and> i v0 = w
           then \<forall>v0. v0 \<in> world fM \<and>
                     i v0 = w \<longrightarrow>
                     V p v0
           else False) \<longrightarrow>
          p \<in> props sig \<and> w \<in> i ` world fM"
     by presburger
 qed
  have 
   c2:"(\<forall>m wl.
        iR m wl \<longrightarrow>
        m \<in> ops sig \<and>
        length wl = arity sig m + 1 \<and>
        (\<forall>w. w \<in> list.set wl \<longrightarrow>
             w \<in> elts Wv))"  unfolding iR_def eWv W_def 
  proof-
    {fix m wl
      assume 
      a1:"\<exists>wl0. list.set wl0 \<subseteq> world fM \<and>
                 map i wl0 = wl"
      and 
      a2: "\<forall>wl0. list.set wl0 \<subseteq> world fM \<and>
                   map i wl0 = wl \<longrightarrow>
                   R m wl0"
      from a1 obtain wl0 where 
      wl0_ss_fM: " list.set wl0 \<subseteq> world fM"
      and iwl0: " map i wl0 = wl"
        by blast
      with a2 have "R m wl0" by metis
      then have 1: "m \<in> ops sig" using  is_struct_fM
        unfolding R_def is_struct_def by blast
      have 2:" length wl = arity sig m + 1"
       using  is_struct_fM[unfolded is_struct_def]
       using R_def \<open>R m wl0\<close> iwl0 by force
     have 
     3:"(\<forall>w. w \<in> list.set wl \<longrightarrow>
            w \<in> i ` world fM) " using a1
       by fastforce
     from 1 2 3 have 
     " m \<in> ops sig \<and>
       length wl = arity sig m + 1 \<and>
       (\<forall>w. w \<in> list.set wl \<longrightarrow>
            w \<in> i ` world fM)" by metis
   }
   then show
   " \<forall>m wl.
       (if \<exists>wl0. list.set wl0 \<subseteq> world fM \<and>
                 map i wl0 = wl
        then \<forall>wl0. list.set wl0 \<subseteq> world fM \<and>
                   map i wl0 = wl \<longrightarrow>
                   R m wl0
        else False) \<longrightarrow>
       m \<in> ops sig \<and>
       length wl = arity sig m + 1 \<and>
       (\<forall>w. w \<in> list.set wl \<longrightarrow>
            w \<in> i ` world fM)"
     by presburger
 qed

   have "is_Vstruct sig iM"
     unfolding iM_def is_Vstruct_def is_struct_def 
      Vstruct2struct_def fst_conv snd_conv
    
     using \<open>i fw \<in> elts Wv\<close> c1 c2 by blast
   have fwfM:"fw \<in> world fM" using asatis_in_world
     by (metis sat)
   from sat have "Vsatis iM (i fw) \<phi>" 
     unfolding Vsatis_def Vstruct2struct_def iM_def fst_conv snd_conv eWv
     using  inj_asatis[OF inj_i fwfM, of \<phi>] sat
     unfolding inj_struct_def inj_rel_def iR_def inj_valt_def iV_def
    R_def V_def W_def by blast
   then show ?thesis
     using \<open>finite (Vworld iM)\<close> \<open>is_Vstruct sig iM\<close> \<open>tree (ops sig) (Vworld iM, Vrel iM) (i fw)\<close> 
     by blast
 qed

definition Vequiv where 
"Vequiv phi1 phi2 \<equiv> \<forall>M w. Vsatis M w phi1 \<longleftrightarrow> Vsatis M w phi2"

lemma Vequiv_small_type:
  assumes Veq:"Vequiv phi1 phi2"
  and s:"small (UNIV :: 'a set)"
  shows "cequiv TYPE('a) phi1 phi2" unfolding cequiv_def
proof -
  show "\<forall>M w::'a. asatis M w phi1 = asatis M w phi2"
  proof (intro allI)
  fix M ::"'a set \<times> ('b \<Rightarrow> 'a list \<Rightarrow> bool) \<times> ('c \<Rightarrow> 'a \<Rightarrow> bool)" 
  fix w :: "'a"
  show "asatis M w phi1 = asatis M w phi2"
  proof -
  from s have sw:"small (world M)"
    by (meson UNIV_I smaller_than_small subsetI)
  from s obtain inc:: "'a \<Rightarrow> V" where inc: "inj inc"
    and 
  "range inc \<in> range elts"
    by (meson small_def)
    then have "small (inc ` (world M))" 
      using sw by blast
    have eq1:"asatis M w phi1 \<equiv> asatis (copy inc M) (inc w) phi1"
      using copy_asatis[OF inc].
    have eq2:"asatis M w phi2 \<equiv> asatis (copy inc M) (inc w) phi2"
      using copy_asatis[OF inc].
    obtain VW where "elts VW = inc ` (world M)" 
      by (metis \<open>small (inc ` world M)\<close> small_iff)
    then have 
    copyeq:"copy inc M = 
   Vstruct2struct (VW, rel (copy inc M),valt (copy inc M))"
      by (simp add: Vstruct2struct_def copy_def)
    have "Vsatis (VW, rel (copy inc M),valt (copy inc M)) (inc w) phi1 \<equiv> 
         Vsatis (VW, rel (copy inc M),valt (copy inc M)) (inc w) phi2"
      using Veq by (smt (verit) Vequiv_def)
    then have "asatis (copy inc M) (inc w) phi1 \<equiv> asatis (copy inc M) (inc w) phi2"
      unfolding Vsatis_def using copyeq by force
    then show "asatis M w phi1 = asatis M w phi2" using eq1 eq2 by auto
  qed
qed
qed


end