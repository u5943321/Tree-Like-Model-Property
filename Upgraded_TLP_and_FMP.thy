(* Title:        Part of the Modal Model Theory project
 * Content:      Proof of the refined version of the tree-like property and
                 the finite model property to be used in the proof in HOLZF.
 *)




theory Upgraded_TLP_and_FMP
imports Main Modal_Syntax Modal_Model Modal_Semantics 
          Bounded_Morphism Generated_Submodel "n-Bisimulation"
           Tree_Like_Model "deg_wffs" Finite_Model
begin

lemma  tree_like_property1:
  assumes M:"is_struct sig M" 
  and phi: "wff sig phi"
  and s0: "csatis sig M w phi"
shows "\<exists>M' .
 world M' \<subseteq> {l. set l \<subseteq> world M} \<and>
 is_struct sig M'\<and> tree (ops sig) (world M',rel M') [w] \<and> csatis sig M' [w] phi"
  using assms 
proof -
  have w:"w \<in> world M"  using csatis_in_world [OF M s0].
  have p2:"w \<in> generated_set (ops sig) (rel M) {w}" 
    using generated_set_contns_generators 
    by fastforce
  have p4:"{w} \<subseteq> world M"  using w by auto 
  have p5: "{w}\<noteq> {}" by blast
  define W1 where "W1 = generated_set (ops sig) (rel M) {w}"
  define R1 where "R1 = restrict_rel (rel M) (generated_set (ops sig) (rel M) {w})"
  define V1 where "V1 = restrict_valt (valt M) (generated_set (ops sig) (rel M) {w})"
  have sr:"csatis sig (W1,R1,V1) w phi" (is "csatis sig (?W1,?R1,?V1) w phi") 
    unfolding W1_def R1_def V1_def
    using Blackburn_prop_2_6[OF M p2 phi p4 p5] s0 by metis (*tedious*)
  have t: "tree (ops sig) (unrav_seq w (ops sig) R1, unrav_rel w (ops sig) R1) 
       [w]" using tree_unrav[of "ops sig" w "R1"].
  define M1 where "M1 = (W1,R1,V1)"
  have M1: "is_struct sig M1" 
    unfolding M1_def W1_def R1_def V1_def 
    using gen_substruct_is_struct[of sig M "{w}", OF M p4 p5].
  have wM1: "w \<in> world M1" 
    unfolding M1_def W1_def using p2 by simp
  define W' where "W' = unrav_seq w (ops sig) (rel M1)"
  define R' where "R' = unrav_rel w (ops sig) (rel M1)"
  define V' where "V' = unrav_valt (unrav_seq w (ops sig) (rel M1)) (valt M1)"
  have bounded_morphism : "bounded_morphism sig last (W',R',V') M1" 
    unfolding W'_def R'_def V'_def
   using  Blackburn_prop_2_15_bounded_morphism[of w M1 sig] M1
    using  M1 wM1 by fastforce
  have M': "is_struct sig (W',R',V')" 
   unfolding W'_def R'_def V'_def using unrav_is_struct
   by (metis M1 wM1)
  have "W' \<subseteq>  {l. set l \<subseteq> world M1}"  using 
  Blackburn_prop_2_15_bounded_morphism_in_world[of w M1 sig,OF wM1 M1]
   
  proof -
    {fix l assume l:"l \<in> unrav_seq w (ops sig) (rel M1)"
      from
      Blackburn_prop_2_15_bounded_morphism_in_world[of w M1 sig l ops,OF wM1 M1 l]
      have "set l \<subseteq> world M1" 
        by blast
    }
    then show "W' \<subseteq>  {l. set l \<subseteq> world M1}"
      unfolding W'_def 
      by blast
  qed
  have "world M1\<subseteq> world M"
    by (metis M M1_def W1_def generated_set_subset_world p4 split_pairs subsetI)
  have "[w] \<in> W'" 
    unfolding W'_def 
    by (simp add: unrav_seq.intros(1))
  then have wW':"[w] \<in> world (W',R',V')" by simp
  have "csatis sig (W',R',V') [w] phi" 
    unfolding M1_def
    using Blackburn_prop_2_14 [of sig "(W',R',V')" M1,OF M' M1 bounded_morphism wW' phi,unfolded M1_def] sr
    by auto
  then show ?thesis using t 
    using M1_def R'_def W'_def M'
    using \<open>W' \<subseteq> {l. set l \<subseteq> world M1}\<close>
    using \<open>world M1 \<subseteq> world M\<close> by auto
qed


lemma  tree_like_property_ss:
  assumes M:"is_struct sig M" 
  and phi: "wff sig phi"
  and s0: "asatis M w phi"
shows "\<exists>M' . world M' \<subseteq> {l. set l \<subseteq> world M} \<and> is_struct sig M' \<and> tree (ops sig) (world M',rel M') [w] \<and> asatis M' [w] phi"
  using tree_like_property1 csatis_asatis assms
  by metis
  


definition restrict_sig_rel where 
"restrict_sig_rel ms M m wl \<equiv> if m \<in> ms then rel M m wl else False"

definition restrict_sig_valt where
"restrict_sig_valt ps M v p \<equiv> if v \<in> ps then valt M v p else False"

definition restrict_sig_struct where
"restrict_sig_struct msps M \<equiv> (world M, restrict_sig_rel (fst msps) M,restrict_sig_valt (snd msps) M)"

lemma restrict_sig_struct_struct:
  assumes "is_struct sig M"
  shows "is_struct (restrict_sig sig ms ps) 
         (restrict_sig_struct (ms,ps) M)"
  unfolding is_struct_def  restrict_sig_valt_def restrict_sig_rel_def
restrict_sig fst_conv snd_conv restrict_sig_struct_def     
  by (metis IntI assms is_struct_def)

lemma satis_all_P':
  assumes w1:"w1 \<in> world M1"
   and w2:"w2 \<in> world M2"
   and Pimp: "\<And>phi. P phi \<Longrightarrow> P (cNOT phi)"
   and asm:"\<And>phi. P phi \<Longrightarrow>
        asatis M2 w2 phi \<Longrightarrow> asatis M1 w1 phi"
    and P:"P phi"
  shows
        "asatis M1 w1 phi = asatis M2 w2 phi"
 
  by (meson P Pimp asm in_world_sat_or_not not_satis_and_cNOT w2)



lemma satis_all_deg_n':
  assumes w1:"w1 \<in> world M1"
   and w2:"w2 \<in> world M2"
   and eqk:"\<And>phi.  phi \<in> deg_wffs k sig \<Longrightarrow>
        asatis M2 w2 phi \<Longrightarrow> asatis M1 w1 phi"
    and deg:" phi \<in> deg_wffs k sig"
  shows
        "asatis M1 w1 phi = asatis M2 w2 phi"
  using satis_all_P'
  by (smt (verit, del_insts) deg eqk satis_all_deg_n w1 w2)


lemma sig_restrict_wff:
  assumes "wff sig f"
  and "modal_operators f \<subseteq> ms"
  and "prop_letters f \<subseteq> ps"
shows "wff (restrict_sig sig ms ps) f" using assms
proof (induction f)
  case cFALSE
  then show ?case 
    by (simp add: wff.cFALSE)
next
  case (cVAR p)
  then show ?case
    by (simp add: restrict_sig wff.cVAR)
next
  case (cDISJ f1 f2)
  then show ?case 
    by (simp add: wff_cDISJ)
next
  case (cNOT f)
  then show ?case
    by (simp add: wff.cNOT)
next
  case (cDIAM m fl)
  then show ?case  
    by (smt (verit, ccfv_threshold) IntI fst_conv modal_operators_cDIAM_subseteq
 prop_letters_cDIAM_subseteq restrict_sig snd_conv wff.cDIAM)
qed


lemma restrict_sig_struct_asatis:
  assumes "asatis M w f"
shows "asatis (restrict_sig_struct (modal_operators f,prop_letters f) M) w f"
  using equi_asatis_restrict_sig 
by (smt (verit, best) assms fst_conv restrict_sig_struct_def restrict_sig_rel_def 
  restrict_sig_valt_def snd_conv)

lemma wff_sig_prop_letters_subseteq:
  assumes "wff sig f"
  shows "prop_letters f \<subseteq> props sig" using assms
proof (induction f)
  case (cVAR x)
  then show ?case 
    by simp
next
  case cFALSE
  then show ?case
    by simp
next
  case (cDISJ f1 f2)
  then show ?case 
    by auto
next
  case (cNOT f)
  then show ?case
    by simp
next
  case (cDIAM x1a x2)
  then show ?case 
    by auto
qed


lemma wff_sig_modal_operators_subseteq:
  assumes "wff sig f"
  shows "modal_operators f \<subseteq> ops sig" using assms
proof (induction f)
  case (cVAR x)
  then show ?case 
    by simp
next
  case cFALSE
  then show ?case
    by simp
next
  case (cDISJ f1 f2)
  then show ?case 
    by auto
next
  case (cNOT f)
  then show ?case
    by simp
next
  case (cDIAM x1a x2)
  then show ?case by auto
qed


lemma asatis_struct_sig_restriction:
  assumes "is_struct sig M"
  and "wff sig f"
  and "asatis M w f"
defines "sig' \<equiv> restrict_sig sig ( modal_operators f) (prop_letters f)" 
defines "M' \<equiv> (restrict_sig_struct (modal_operators f,prop_letters f) M)"
shows " ops sig' = modal_operators f \<and>  props sig' = prop_letters f \<and>
        wff sig' f \<and> is_struct sig' M' 
       \<and> asatis M' w f \<and> world M' \<subseteq> world M" 
  by (metis Int_absorb1 M'_def assms(1) assms(2) assms(3) dual_order.refl fst_conv restrict_sig
  restrict_sig_struct_asatis restrict_sig_struct_def restrict_sig_struct_struct sig'_def 
  sig_restrict_wff snd_conv wff_sig_modal_operators_subseteq wff_sig_prop_letters_subseteq)



lemma asatis_struct_sig_restriction_packed:
  assumes "is_struct sig M"
  and "wff sig f"
  and "asatis M w f"
shows 
 "\<exists>sig' M'. ops sig' = modal_operators f \<and>  props sig' = prop_letters f \<and>
        wff sig' f \<and> is_struct sig' M' 
       \<and> asatis M' w f"
  by (meson asatis_struct_sig_restriction assms(1) assms(2) assms(3))

lemma is_struct_rel_ss_world:
  assumes "is_struct sig M"
  shows "rset (ops sig) (rel M) \<subseteq> world M"
  unfolding is_struct_def
  by (metis (no_types, lifting) assms in_rset is_struct_def subsetI)

theorem Finite_Tree_Model_Property:
  assumes "wff sig00 \<phi>"
  and "asatis M00 (w00 ::'a) \<phi>"
assumes "is_struct sig00 M00"
defines "sig \<equiv> restrict_sig sig00 ( modal_operators \<phi>) (prop_letters \<phi>)"
shows 
  "\<exists>fM fw. is_struct sig fM \<and>
           world fM \<subseteq> {l. set l \<subseteq> world M00} \<and>
           finite (world fM) \<and> 
           tree (ops sig) (world fM,rel fM) (fw :: 'a list) \<and> 
           asatis fM fw \<phi>"
proof - 
  have osig: "ops sig = modal_operators \<phi>"
    by (simp add: Int_absorb1 assms(1) restrict_sig sig_def wff_sig_modal_operators_subseteq)
  
  have msig: "props sig = prop_letters \<phi>"
    by (simp add: Int_absorb1 assms(1) restrict_sig sig_def wff_sig_prop_letters_subseteq)
  have fin_osig: "finite (ops sig)" 
    using modal_operators_finite osig by fastforce
  have fin_psig: "finite (props sig)"
    by (simp add: msig prop_letters_finite)
  have wff: "wff sig \<phi>" 
    by (simp add: assms(1) sig_def sig_restrict_wff)
  from assms obtain M0 w0 where 
  M0: "is_struct sig M0" and w0: "asatis M0 (w0::'a) \<phi>"
  and M0_s:"world M0 \<subseteq> world M00"
    using asatis_struct_sig_restriction
    by metis
   
  define r where "r \<equiv> [w0]"
  from tree_like_property_ss[OF M0 wff w0] r_def obtain tM where 
  tM: "is_struct sig tM" 
  and tM_s: "world tM \<subseteq> {l. set l \<subseteq> world M0}"
  and tree_tM : "tree (ops sig) (world tM, rel tM) r" 
  and tM_phi: "asatis tM r \<phi>" by blast
  define k where "k \<equiv> deg \<phi>"
  define D where "D \<equiv>  (cDIAM_deg_wff_reps TYPE('a list) k sig)"
  then have fin_D: "finite D" using finite_cDIAM_deg_wff_reps fin_osig fin_psig 
    by blast
  have Ddw:"D \<subseteq> deg_wffs k sig" using cDIAM_deg_wff_reps_deg_wffs D_def by blast
  have mop:"\<Union> (modal_operators ` D) \<subseteq> ops sig" using wff_sig_modal_operators_subseteq
   Ddw deg_wffs_def  by blast
 
  from D_def cDIAM_deg_wff_reps_properties' have 
  D_prop:"\<And>m fl tw. cDIAM m fl \<in> deg_wffs k sig \<Longrightarrow>
          asatis tM tw (cDIAM m fl) \<Longrightarrow>
  \<exists>fl'. cDIAM m fl' \<in> D \<and> cequiv TYPE('a list) (cDIAM m fl) (cDIAM m fl') \<and>
        length fl = length fl' \<and> 
        (\<forall>j. j <length fl \<longrightarrow> cequiv TYPE('a list) (fl ! j) (fl' ! j)) "
    by (metis infinite_UNIV_listI)

  have 
  "\<And>m fl v. \<exists>wl. asatis tM v (cDIAM m fl) \<longrightarrow>
         length wl = length fl \<and>
              rel tM m (v # wl) \<and> 
              (\<forall>w f. (w,f) \<in> set (zip wl fl) \<longrightarrow> asatis tM w f)"
    unfolding asatis.simps 
    by blast
  then obtain cwl0 where 
  cwl0:"\<And>m fl v. asatis tM v (cDIAM m fl) \<Longrightarrow>
           length (cwl0 m fl v) = length fl \<and>
              rel tM m (v # (cwl0 m fl v)) \<and> 
              (\<forall>w f. (w,f) \<in> set (zip (cwl0 m fl v) fl) \<longrightarrow> 
                asatis tM w f)"
  proof -
    assume "\<And>cwl. (\<And>m fl v. asatis tM v (cDIAM m fl) \<Longrightarrow> length (cwl m fl v) = length fl \<and> rel tM m (v # cwl m fl v) \<and> (\<forall>w f. (w, f) \<in> set (zip (cwl m fl v) fl) \<longrightarrow> asatis tM w f)) \<Longrightarrow> thesis"
    then show ?thesis
      using \<open>\<And>v m fl. \<exists>wl. asatis tM v  (cDIAM m fl) \<longrightarrow> length wl = length fl \<and> rel tM m (v # wl) \<and> (\<forall>w f. (w, f) \<in> set (zip wl fl) \<longrightarrow> asatis tM w f)\<close> by moura
  qed
  define cwl where "cwl \<equiv> \<lambda>f. case f of cDIAM m0 fl0 \<Rightarrow> cwl0 m0 fl0
                                                    |_ \<Rightarrow> undefined"
  then have
  cwl:"\<And>m fl v. asatis tM v (cDIAM m fl) \<Longrightarrow>
           length (cwl (cDIAM m fl) v) = length fl \<and>
              rel tM m (v # (cwl (cDIAM m fl) v)) \<and> 
              (\<forall>w f. (w,f) \<in> set (zip (cwl (cDIAM m fl) v) fl) \<longrightarrow> 
                asatis tM w f)" 
    by (simp add: cwl0)
  have cwl_ss: "\<And>m fl v. asatis tM v (cDIAM m fl) \<Longrightarrow>
                 set (cwl (cDIAM m fl) v) \<subseteq> world tM"
    using tM cwl asatis_in_world 
    by (metis (no_types, opaque_lifting) in_set_impl_in_set_zip1 subset_code(1))
  define fws where "fws \<equiv> fin_worlds tM r D cwl k"
  define M' where "M' \<equiv> (fws,restrict_rel (rel tM) fws,
                     restrict_valt (valt tM) fws)" 
  define Op where "Op \<equiv> ops sig"
  have fws_ss: "fws \<subseteq> world tM" using fin_worlds_subseteq_world cwl
   by (metis asatis_in_world cwl_ss fws_def tM_phi)
  have M':"is_struct sig M'" using restrict_struct_struct[OF tM,of fws]
    unfolding M'_def fws_def
    by (metis ex_in_conv nth_world_fin_world_cases)
  have rsss: "rset (ops sig) (rel tM) \<subseteq> world tM"
    using is_struct_rel_ss_world[OF tM].
  have TREE:"tree Op (fws,restrict_rel (rel tM) fws) r" 
    using tree_nth_worlds_tree[OF tree_tM rsss _ _ _ mop] cwl
    unfolding fws_def Op_def by blast
  have FIN:"finite fws" unfolding fws_def
    using fin_worlds_finite[OF fin_D, of tM cwl r k] cwl 
    by blast
  have "\<And>Z. n_bisim Z k tM M' r r \<Longrightarrow> asatis M' r \<phi>"
    using Blackburn_prop2_31_L2R[OF tM M' , of _ k r r \<phi>] csatis_asatis[OF M']
   by (metis  csatis_asatis dual_order.refl k_def tM tM_phi)
 define Z where "Z \<equiv>
         \<lambda>n v v'. 
          v \<in> world tM \<and> v' \<in> world M' \<and>
          height r Op (rel tM) v = height r Op (rel tM) v' \<and> 
          height r Op (rel tM) v' \<le> k - n \<and> 
          (\<forall>psi. psi \<in> deg_wffs n sig \<longrightarrow> 
             (asatis tM v psi = asatis tM v' psi))" 
  
  have r: "r \<in> fws" using root_in_fin_worlds fws_def
    by simp
  have 
   "\<And> i v v'.
        Z i v v' \<Longrightarrow>
        v \<in> world tM \<and> v' \<in> world M'" using Z_def
    by blast
  {fix i v v'
    assume "i + 1 \<le>k"
    then have "Z (i + 1) v v' \<longrightarrow> Z i v v'"
      unfolding Z_def
    by (simp add: Nat.le_diff_conv2 deg_wffs_def)
  }
  have rtM:"r \<in> world tM" using tree_def tree_tM
    by (simp add: root_in_tree)
  have rM':"r \<in> world M'" using root_in_fin_worlds M'_def
   using \<open>r \<in> fws\<close> by auto  
  have 
   "Z k r r" unfolding Z_def root_height_0
    using rtM rM'  by blast
  {fix v v' p
    assume Z0vv': "Z 0 v v'"
    then have " valt tM p v = valt M' p v'"
    proof - 
      (*M M' are sig structs so if p is not in sig both give false*)
      consider (c1) "p \<in> props sig" | 
              (c2) "p \<notin> props sig" by metis
      then show ?thesis 
      proof cases
        case c1
        then show ?thesis
        proof -
          from c1 have "wff sig (cVAR p)" 
            unfolding wff_cVAR by simp
          with Z0vv'
          have vv'p:"asatis tM v (cVAR p) = asatis tM v' (cVAR p)"
            unfolding Z_def
            using deg.simps(2) 
            by (metis (no_types, lifting) bot_nat_0.extremum deg_wffs_def mem_Collect_eq)
          from Z0vv' Z_def have vM:"v \<in> world tM" by simp
          from Z0vv' Z_def have v'M':"v' \<in> world M'" by simp
          from vM v'M' vv'p show "valt tM p v = valt M' p v'" 
            by (metis tM M'_def asatis.simps(2) fst_conv is_struct_def restrict_valt_def snd_conv)
           qed
          
      next
        case c2
        then show ?thesis using tM M' is_struct_def  by metis
      qed
    qed
  } 
  
  from tree_height_rel_lemma[OF tree_tM rsss]
  have hstep:"\<And> w vl m v. w \<in> world tM \<Longrightarrow> rel tM m (w # vl) \<Longrightarrow> v \<in> set vl \<Longrightarrow>
        height r Op (rel tM) v = height r Op (rel tM) w + 1"
    unfolding Op_def
    using is_struct_def tM by metis
  {fix i w 
    assume nw:"nth_world tM r D cwl i w"
    have "height r Op (rel tM) w = i" using nw
    proof (induction rule: nth_world.induct)
      case zero
      then show ?case 
        by (simp add: root_height_0)
    next
      case (suc n v m fl w)
      from fws_ss suc(1) have v:"v \<in> world tM" 
        using suc.hyps(3) by auto
      then show ?case using hstep[OF v] cwl
        using suc.IH suc.hyps(3) suc.hyps(4) by blast
    qed
  }
  then have 
  nw_height:"\<And>i w. nth_world tM r D cwl i w \<Longrightarrow> height r Op (rel tM) w = i"
    by blast

  { fix i v v' ul m
    assume ile: "i + 1 \<le> k"
    and Zvv':"Z (i + 1) v v'" 
    and rvul:"rel tM m (v # ul)"
    then have m:"m \<in> ops sig" using is_struct_def tM by metis
    have 
    feq: "\<And>f. f \<in> deg_wffs (i+1) sig \<Longrightarrow>
             (asatis tM v f = asatis tM v' f) "
    using Z_def Zvv' by blast
    from Zvv' Z_def have v:"v \<in> world tM" by blast
    from Zvv' Z_def have v':"v' \<in> world M'" by blast
    from Zvv' Z_def have hvv':"height r Op (rel tM) v = height r Op (rel tM) v'" by blast 
    from Zvv' Z_def have hv':"height r Op (rel tM) v' \<le> k - (i+1)" by blast
    from rvul tM is_struct_def have sul:"set ul \<subseteq> world tM" 
      by (metis (no_types, lifting) set_subset_Cons subset_code(1))
    from bigconj_deg_wffs_mk_cDIAM[OF sul fin_psig fin_osig, of i ]
    obtain phil where 
      lenphil:"length phil = length ul" and
      dt:"\<And>u phi. (u, phi) \<in> set (zip ul phil) \<Longrightarrow> 
         deg_thy TYPE('a list) i sig tM u phi " by blast
    from lenphil tM is_struct_def rvul have art:"length phil = arity sig m"
     by (metis Suc_eq_plus1 add_right_imp_eq length_Cons)
    from dt m have d_m_phil:"cDIAM m phil \<in> deg_wffs (i+1) sig"
      using deg_wffs.deg_thy_def deg_wffs_cDIAM_step[OF _ m art]
      by (metis in_set_impl_in_set_zip2 lenphil)
    with ile have d_m_phil_k: "cDIAM m phil \<in> deg_wffs k sig"
      using deg_wffs_def 
      by (metis (no_types, lifting) le_trans mem_Collect_eq)
    from dt have 
    "\<And>u phi. (u, phi) \<in> set (zip ul phil) \<Longrightarrow> 
           asatis tM u phi" 
      using deg_thy_satis_self by metis
    with rvul v sul asatis.simps have "asatis tM v (cDIAM m phil)"
      using lenphil by auto
    with feq[OF d_m_phil] have v'sat: "asatis tM v' (cDIAM m phil)" by simp
    (*maybe the height value not important , only want the suc
        to be counted into the world*)
    from v'[unfolded M'_def fst_conv fws_def fin_worlds_def nth_worlds_def] 
    obtain n where n:"nth_world tM r D cwl n v'"
      by blast
    with nw_height hv' have "n \<le> k - (i + 1)" by blast
    with ile have n1:"n + 1 \<le> k" by linarith
    from D_prop[OF d_m_phil_k v'sat]
    obtain fl' where 
    d_m_fl'_D:"cDIAM m fl' \<in> D" and 
    d_m_fl'_eqv:"cequiv TYPE('a list) (cDIAM m phil) (cDIAM m fl')" and
    "length phil = length fl'" and 
    philfl':"\<And>j. j <length phil \<Longrightarrow>  cequiv TYPE('a list) (phil ! j) (fl' ! j)"
      by blast
    then have
    philfl'eq:"\<And>phi f'. (phi,f')\<in> set (zip phil fl') \<Longrightarrow> cequiv TYPE('a list) phi f'"
      by (metis in_zip_ith)
    from d_m_fl'_eqv cequiv_def v'sat have v'sat':"asatis tM v' (cDIAM m fl')"
      by metis
    from nth_world.suc[OF n d_m_fl'_D v'sat'] 
    have "\<And>w. w \<in> set (cwl (cDIAM m fl') v') \<Longrightarrow> nth_world tM r D cwl (n + 1) w ".
    
    then have cwlss:"set (cwl (cDIAM m fl') v') \<subseteq> fws" using nth_world_fin_worlds[OF n1]
     by (metis fws_def subsetI)

    define ul' where "ul'\<equiv> (cwl (cDIAM m fl') v') "
    from cwl[OF v'sat'] ul'_def
    have lenul':"length ul' = length fl'" by blast
    from cwl[OF v'sat'] ul'_def have rv'ul':"rel tM m (v' # ul')" by blast
    from cwl[OF v'sat'] ul'_def have
      ul'fl'sat:"\<And>w f. (w, f) \<in> set (zip ul' fl') \<Longrightarrow> asatis tM w f" by blast
    from rv'ul' cwlss have rv'ul'M':"rel M' m (v' # ul')" 
      unfolding M'_def fst_conv snd_conv using restrict_rel_def
      by (metis (no_types, lifting) M'_def fst_conv set_ConsD subset_iff ul'_def v')
    have 
   ul_height:"\<And>u. u \<in> set ul \<Longrightarrow> height r Op (rel tM) u =  
    (height r Op (rel tM) v) + 1" using hstep[OF v rvul]
      by blast
    have v'tM:"v' \<in> world tM" using fws_ss v' unfolding M'_def fst_conv snd_conv
      by blast
    have 
    ul'_height: "\<And>u'. u' \<in> set ul' \<Longrightarrow> height r Op (rel tM) u' =  
    (height r Op (rel tM) v') + 1" using hstep[OF v'tM rv'ul']
      by blast
    have 
    "\<And> u u'. (u, u') \<in> set (zip ul ul') \<Longrightarrow> 
      height r Op (rel tM) u =  height r Op (rel tM) u'"
      using ul_height ul'_height hvv' 
      by (metis set_zip_leftD set_zip_rightD)
    from ul'_height ile hv' have
     "\<And>u'. u' \<in> set ul' \<Longrightarrow> height r Op (rel tM) u' \<le> k - i" 
      by auto
    have 
    "\<And>u u' phi.
       (u, u') \<in> set (zip ul ul') \<Longrightarrow>
       phi \<in> deg_wffs i sig \<Longrightarrow> asatis tM u phi = asatis tM u' phi" 
    proof - 
      fix  u u' phi 
      assume uu':"(u, u') \<in> set (zip ul ul')"
      and phi:"phi \<in> deg_wffs i sig"
      show "asatis tM u phi = asatis tM u' phi" 
      proof  (rule satis_all_deg_n)
        show "u \<in> world tM" 
          by (meson \<open>(u, u') \<in> set (zip ul ul')\<close> set_zip_leftD subsetD sul)
        show "u' \<in> world tM"  using cwlss 
          using \<open>(u, u') \<in> set (zip ul ul')\<close> fws_ss set_zip_rightD ul'_def by fastforce
        show "phi \<in> deg_wffs i sig" using phi deg_wffs_def  by blast
        from dt ul'fl'sat  philfl'eq
        show 
        "\<And>phi. phi \<in> deg_wffs i sig \<Longrightarrow> asatis tM u phi \<Longrightarrow> asatis tM u' phi"
        proof - 
          have len_ul_phil:"length ul = length phil" by (simp add: lenphil)
          have "length ul' = length fl'" using lenul' by linarith
          have "length ul = length ul'" using lenul'
            using \<open>length phil = length fl'\<close> lenphil by auto
          obtain phi0 f0 where
          "(u, phi0) \<in> set (zip ul phil)" and 
          "(phi0,f0) \<in> set (zip phil fl')" and 
          "(u',f0) \<in> set (zip ul' fl')" using in_zip_ith
            by (metis \<open>length ul = length ul'\<close> len_ul_phil lenul' uu')
          then have 
          "asatis tM u' f0"using ul'fl'sat  
            by blast
          then have 
          satu':"asatis tM u' phi0" using  philfl'eq cequiv_def
            by (metis \<open>(phi0, f0) \<in> set (zip phil fl')\<close>)
          have "deg_thy TYPE('a list) i sig tM u phi0"
            using dt \<open>(u, phi0) \<in> set (zip ul phil)\<close> by blast
          with satu' show
          "\<And>phi. phi \<in> deg_wffs i sig \<Longrightarrow> asatis tM u phi \<Longrightarrow> asatis tM u' phi"
            using deg_thy_def by metis
          
        qed 
      qed
    qed
    then have 
    "(\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')" unfolding Z_def
      by (smt (verit, best) M'_def \<open>\<And>u' ua. (ua, u') \<in> set (zip ul ul') \<Longrightarrow> 
     height r Op (rel tM) ua = height r Op (rel tM) u'\<close> 
     \<open>\<And>u'. u' \<in> set ul' \<Longrightarrow> height r Op (rel tM) u' \<le> k - i\<close> 
    cwlss fst_conv set_zip_leftD set_zip_rightD subsetD sul ul'_def)
    with rv'ul'M' have "\<exists>ul'. rel M' m (v' # ul') \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')" 
      by metis
  }
  {fix i v v' ul' m
    assume ile: "i + 1 \<le> k"
    and Zvv':"Z (i + 1) v v'" 
    and r'v'ul': "rel M' m (v' # ul')"
     then have m:"m \<in> ops sig" using is_struct_def M' by metis
    have 
    feq: "\<And>f. f \<in> deg_wffs (i+1) sig \<Longrightarrow>
             (asatis tM v f = asatis tM v' f) "
    using Z_def Zvv' by blast
    from Zvv' Z_def have v:"v \<in> world tM" by blast
    from Zvv' Z_def have v':"v' \<in> world M'" by blast
    from Zvv' Z_def have hvv':"height r Op (rel tM) v = height r Op (rel tM) v'" by blast 
    from Zvv' Z_def have hv':"height r Op (rel tM) v' \<le> k - (i+1)" by blast
    from r'v'ul' M' is_struct_def have sul':"set ul' \<subseteq> fws" 
      by (metis (no_types, lifting) M'_def fst_conv set_subset_Cons subset_iff)
    then have sul'1:"set ul' \<subseteq> world tM"   using fws_ss by auto
    from bigconj_deg_wffs_mk_cDIAM[OF sul'1 fin_psig fin_osig, of i ]
    obtain phil where 
      lenphil:"length phil = length ul'" and
      dt:"\<And>u phi. (u, phi) \<in> set (zip ul' phil) \<Longrightarrow> 
         deg_thy TYPE('a list) i sig tM u phi " by blast
    from lenphil tM is_struct_def r'v'ul' have art:"length phil = arity sig m"
      by (metis M' Suc_eq_plus1 add_right_imp_eq length_Cons)
    from dt m have d_m_phil:"cDIAM m phil \<in> deg_wffs (i+1) sig"
      using deg_wffs.deg_thy_def deg_wffs_cDIAM_step[OF _ m art]
      by (metis in_set_impl_in_set_zip2 lenphil)
    with ile have d_m_phil_k: "cDIAM m phil \<in> deg_wffs k sig"
      using deg_wffs_def 
      by (metis (no_types, lifting) le_trans mem_Collect_eq)
    from dt have 
    "\<And>u phi. (u, phi) \<in> set (zip ul' phil) \<Longrightarrow> 
           asatis tM u phi" 
      using deg_thy_satis_self by metis
    with r'v'ul' v sul'1 asatis.simps have "asatis tM v' (cDIAM m phil)"
      using lenphil 
      by (smt (verit, del_insts) M'_def fst_conv fws_ss in_mono restrict_rel_def snd_conv v')
    with feq[OF d_m_phil] have vsat: "asatis tM v (cDIAM m phil)" by simp
    from v'[unfolded M'_def fst_conv fws_def fin_worlds_def nth_worlds_def] 
    obtain n where n:"nth_world tM r D cwl n v'"
      by blast
    with nw_height hv' have "n \<le> k - (i + 1)" by blast
    with ile have n1:"n + 1 \<le> k" by linarith
    from n have "height r Op (rel tM) v \<le> k - (i + 1) " 
      using hv' hvv' by auto
 have 
   ul'_height:"\<And>u. u \<in> set ul' \<Longrightarrow> height r Op (rel tM) u =  
    (height r Op (rel tM) v') + 1" using hstep 
      by (metis (no_types, lifting) M'_def \<open>asatis tM v' (cDIAM m phil)\<close>
       asatis_in_world r'v'ul' restrict_rel_def split_pairs)
    from vsat obtain ul where 
     lenul:"length ul = length phil"
     and "rel tM m (v # ul)"
     and ulphil:"\<And>w f. (w,f) \<in> set (zip ul phil) \<Longrightarrow> asatis tM w f"
      unfolding asatis.simps by blast
    have v'tM:"v' \<in> world tM" using fws_ss v' unfolding M'_def fst_conv snd_conv
      by blast
    have 
    ul_height: "\<And>u. u \<in> set ul \<Longrightarrow> height r Op (rel tM) u =  
    (height r Op (rel tM) v) + 1" using hstep 
      using \<open>rel tM m (v # ul)\<close> v by blast
     
    have 
    "\<And> u u'. (u, u') \<in> set (zip ul ul') \<Longrightarrow> 
      height r Op (rel tM) u =  height r Op (rel tM) u'"
      using ul_height ul'_height hvv' 
      by (metis set_zip_leftD set_zip_rightD)
    from ul'_height ile hv' have
     "\<And>u'. u' \<in> set ul' \<Longrightarrow> height r Op (rel tM) u' \<le> k - i" 
      by auto
    have 
    "\<And>u u' phi.
       (u, u') \<in> set (zip ul ul') \<Longrightarrow>
       phi \<in> deg_wffs i sig \<Longrightarrow> asatis tM u phi = asatis tM u' phi" 
    proof - 
      fix  u u' phi 
      assume uu':"(u, u') \<in> set (zip ul ul')"
      and phi:"phi \<in> deg_wffs i sig"
      show "asatis tM u phi = asatis tM u' phi" 
      proof  (rule satis_all_deg_n')
        show "u \<in> world tM" 
          by (metis (no_types, lifting) \<open>rel tM m (v # ul)\<close> in_mono in_rset in_set_zipE
             list.set_intros(2) m rsss uu')
        show "u' \<in> world tM" 
          by (meson set_zip_rightD subsetD sul'1 uu')
        show "phi \<in> deg_wffs i sig" using phi deg_wffs_def
          by blast
        have "length ul = length ul'" 
          by (simp add: lenphil lenul)
        have "length phil = length ul" 
          by (simp add: lenul)
        obtain phi0 where 
        "(u,phi0) \<in> set (zip ul phil)"
        and "(u',phi0) \<in> set (zip ul' phil)"
          by (metis \<open>length ul = length ul'\<close> in_zip_ith lenphil uu')
        with dt 
        have "deg_thy TYPE('a list) i sig tM u' phi0" by blast
        from ulphil
        show 
        "\<And>phi. phi \<in> deg_wffs i sig \<Longrightarrow> asatis tM u' phi \<Longrightarrow> asatis tM u phi"
          using deg_thy_def 
          by (metis \<open>(u, phi0) \<in> set (zip ul phil)\<close> \<open>deg_thy TYPE('a list) i sig tM u' phi0\<close>)
       
      qed
    qed
    then have 
    "(\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')" unfolding Z_def
      by (metis (no_types, opaque_lifting) M' \<open>\<And>u' ua. (ua, u') \<in> set (zip ul ul') \<Longrightarrow>
      height r Op (rel tM) ua = height r Op (rel tM) u'\<close> \<open>\<And>u'. u' \<in> set ul' \<Longrightarrow> 
    height r Op (rel tM) u' \<le> k - i\<close> \<open>rel tM m (v # ul)\<close> in_set_zipE is_struct_def list.set_intros(2)
     r'v'ul' tM)
    then have
  "\<exists>ul. rel tM m (v # ul) \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')" 
      using \<open>rel tM m (v # ul)\<close> by blast
  }
  
  then have nbisim: "n_bisim Z k tM M' r r" unfolding n_bisim_def 
    by (meson \<open>Z k r r\<close> \<open>\<And>v' v i. Z i v v' \<Longrightarrow> v \<in> world tM \<and> v' \<in> world M'\<close> 
    \<open>\<And>v' v i. i + 1 \<le> k \<Longrightarrow> Z (i + 1) v v' \<longrightarrow> Z i v v'\<close>
    \<open>\<And>v' v p. Z 0 v v' \<Longrightarrow> valt tM p v = valt M' p v'\<close> 
   \<open>\<And>v' v ul m i. \<lbrakk>i + 1 \<le> k; Z (i + 1) v v'; rel tM m (v # ul)\<rbrakk> 
  \<Longrightarrow> \<exists>ul'. rel M' m (v' # ul') \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')\<close>)
  then have "asatis M' r \<phi>" using tM_phi Blackburn_prop2_31_L2R[OF tM M' nbisim, of \<phi>] 
  k_def csatis_asatis by (metis M' nle_le tM)
  have "world M' \<subseteq> world tM" 
    by (simp add: M'_def fws_ss)
  then have 
  "world M' \<subseteq> {l. set l \<subseteq> world M00}" 
    using M0_s tM_s by force
  then show ?thesis
    using FIN M'_def TREE \<open>asatis M' r \<phi>\<close> Op_def M' by auto
qed







end