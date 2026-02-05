(* Title:        Part of the Modal Model Theory project
 * Content:      Lemmas before constructing a finite model.
                 definition of height. 
                 Define the nth_worlds function that gives the nth-set 
                 in the resultant finite model.
                 properties of the n-th world set in the
                 finite model to be constructed.
 *)



theory Finite_Model
  imports Main Modal_Syntax Modal_Model Modal_Semantics 
          Bounded_Morphism Generated_Submodel "n-Bisimulation"
           Tree_Like_Model "deg_wffs"
begin

inductive height_le ::
 "'a \<Rightarrow> 'm set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool"
  for r :: 'a and Op :: "'m set" and R :: "('m \<Rightarrow> 'a list \<Rightarrow> bool)" 
  where
   root : "height_le r Op R r 0"
 | rel: "height_le r Op R w n \<Longrightarrow> m \<in> Op \<Longrightarrow> R m (w # vl) \<Longrightarrow> v \<in> set vl
        \<Longrightarrow> height_le r Op R v (n+1)"

definition height :: 
"'a \<Rightarrow> 'm set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat" where 
"height r Op R w = Inf {n. height_le r Op R w n}"

lemma is_of_height: 
 "height_le r Op R w n \<and> 
  (\<forall>n'. height_le r Op R w n' \<longrightarrow> n \<le> n') \<Longrightarrow> height r Op R w = n"
  using Orderings.order_class.Least_equality height_def
  by (metis mem_Collect_eq wellorder_InfI wellorder_Inf_le1)

lemma height_le_root:
"height_le r \<tau> R w 0 \<equiv> w = r"
   using height_le.simps 
   by (smt (verit, ccfv_threshold) add_is_0 zero_neq_one)


lemma generated_set_height_le:
  assumes "w \<in> generated_set Op R {r}"
  shows "\<exists>n. height_le r Op R w n" using assms
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case using height_le.root by force
next
  case (2 w m ul u)
  then obtain n where n: "height_le r Op R w n" by blast
  show ?case using height_le.rel[OF n 2(2) 2(3) 2(4)] by blast
qed




lemma height_le_generated_set:
  assumes "height_le r Op R w n"
  shows "w \<in> generated_set Op R {r}" using assms
proof (induction rule:height_le.induct)
  case root
  then show ?case using generated_set.intros(1) by fastforce
next
  case (rel w n m vl v)
  then show ?case using generated_set.intros(2) 
    by metis
qed

lemma generated_set_has_height_le:
 assumes "w \<in> generated_set Op R {r}"
 shows "\<exists>n. height_le r Op R w n" using assms
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case 
    using root by force
next
  case (2 w m ul u)
  then show ?case 
    by (meson rel)
qed

lemma generated_set_height_height_le:
  assumes "w \<in> generated_set Op R {r}"
 shows "height_le r Op R w (height r Op R w)"
  using generated_set_has_height_le height_def 
  by (metis assms mem_Collect_eq wellorder_InfI)

lemma generated_set_height_le_add_1:
  assumes "w \<in> generated_set Op R {r}"
  and "m \<in> Op"
  and "R m (w # vl)"
  and "v \<in> set vl"
shows "height_le r Op R v (height r Op R w + 1)"
  using generated_set_height_height_le height_le.rel 
  by (metis assms(1) assms(2) assms(3) assms(4))


lemma generated_set_height_add_1:
  assumes "w \<in> generated_set Op R {r}"
  and "m \<in> Op"
  and "R m (w # vl)"
  and "v \<in> set vl"
shows "height r Op R v \<le> height r Op R w + 1"
  using generated_set_height_le_add_1 
  by (metis assms(1) assms(2) assms(3) assms(4) 
  height_def mem_Collect_eq wellorder_Inf_le1)
  

definition is_generated_subframe ::
 "'m msig => ('m,'a) frame \<Rightarrow> ('m,'a) frame \<Rightarrow> 'a set \<Rightarrow> bool"
 where
"is_generated_subframe msig F aF X \<equiv>
 is_frame msig F \<and> is_frame msig aF \<and> 
 X \<subseteq> fworld aF \<and>
 fworld F = generated_set (mops msig) (frel aF) X \<and>
 (\<forall>wl m. (\<forall>w. w \<in> set wl \<longrightarrow> w \<in> fworld F) \<longrightarrow> frel F m wl = frel aF m wl)
 "
lemma rooted_has_height:
  assumes "w \<in> generated_set (mops msig) (frel aF) {r}"
   and F:"is_generated_subframe msig F aF {r}"
  shows "\<exists>n. height_le r (mops msig) (frel F) w n" using assms
proof (induction rule:generated_set.induct)
  case (1 x)
  then show ?case using height_le.intros(1) 
    by fastforce 
next
  case (2 w m ul u)
  then obtain a where a : "height_le r (mops msig) (frel F) w a" by metis
  from generated_set.intros(2)[OF 2(1) 2(2) 2(3)] 
  have "\<And>u. u \<in> set ul \<Longrightarrow> u \<in> generated_set (mops msig) (frel aF) {r}"
    by auto
  with 2(3) F have
  Fwul: "frel F m (w # ul)" unfolding is_generated_subframe_def 
    using "2.hyps"(1) by auto
  then show ?case using height_le.intros(2)[OF a 2(2) Fwul 2(4)] by metis
qed

definition is_height_restriction :: 
"('m,'p) sig \<Rightarrow> ('m,'p,'a) struct \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('m,'p,'a) struct \<Rightarrow> bool"
where 
"is_height_restriction sig aM r n M \<equiv> 
 world M = {w. w \<in> world aM \<and> height r (ops sig) (rel aM) w \<le> n} \<and> 
 rel M = restrict_rel (rel aM) (world M) \<and> 
 valt M = restrict_valt (valt aM) (world M)"

lemma is_height_restriction_exists:
 "\<exists>M. is_height_restriction sig aM r n M "
proof - 
  have
  " is_height_restriction sig aM r n
    ({w. w \<in> world aM \<and> height r (ops sig) (rel aM) w \<le> n},
     restrict_rel (rel aM) {w. w \<in> world aM \<and> height r (ops sig) (rel aM) w \<le> n},
     restrict_valt (valt aM) {w. w \<in> world aM \<and> height r (ops sig) (rel aM) w \<le> n})"
    unfolding is_height_restriction_def
    by auto
  then show ?thesis by metis
qed
    
 

lemma is_height_restriction_rel:
  assumes "is_height_restriction sig aM r n M"
  and "\<And>w. w \<in> set wl \<Longrightarrow> w \<in> world M"
shows "rel M m wl = rel aM m wl" using 
 is_height_restriction_def restrict_rel_def 
  by (metis (mono_tags, lifting) assms(1) assms(2))

lemma is_height_restriction_valt:
  assumes "is_height_restriction sig aM r n M"
  and "w \<in> world M"
shows "valt M p w = valt aM p w" using 
 is_height_restriction_def restrict_valt_def
  by (metis (no_types, opaque_lifting) assms(1) assms(2))



lemma is_height_restriction_is_struct:
  assumes aM:"is_struct sig aM"
      and r:"r \<in> world aM"
      and M:"is_height_restriction sig aM r n M"
    shows "is_struct sig M"
proof (unfold is_struct_def,intro conjI)
  have "r \<in> world M" using assms 
    unfolding is_height_restriction_def height_def height_le.intros(1)
    by (metis (no_types, lifting) cInf_eq_minimum mem_Collect_eq
        root zero_le)
  then show "world M \<noteq> {}" by blast
  show " \<forall>p w. valt M p w \<longrightarrow> p \<in> props sig \<and> w \<in> world M"
    using aM M is_height_restriction_def is_struct_def restrict_valt_def
    by (metis (no_types, lifting))
  have r:"\<And>m wl. rel M m wl \<equiv> 
        ((\<forall>w. w \<in> set wl \<longrightarrow> w \<in> world M) \<and> rel aM m wl)"
    using aM M is_height_restriction_def restrict_valt_def
    by (smt (verit, best) restrict_rel_def)
  show "\<forall>m wl. rel M m wl \<longrightarrow> m \<in> ops sig \<and>
  length wl = arity sig m + 1 \<and> (\<forall>w. w \<in> set wl \<longrightarrow> w \<in> world M)"
  proof (intro allI conjI impI)
    show "\<And>m wl. rel M m wl \<Longrightarrow> m \<in> ops sig" unfolding r
      using aM is_struct_def by metis
    show "\<And>m wl. rel M m wl \<Longrightarrow> length wl = arity sig m + 1"
      unfolding r using aM is_struct_def by metis
    show "\<And>m wl w. rel M m wl \<Longrightarrow> w \<in> set wl \<Longrightarrow> w \<in> world M"
      unfolding r using aM by metis
  qed
qed


lemma is_height_restriction_world_subseteq:
  assumes hM:"is_height_restriction sig aM r k M"
  shows "world M \<subseteq> world aM" using assms 
  unfolding is_height_restriction_def 
  by blast

(* lemma 2.33 from Blackburn et al. *)
lemma get_n_bisimulation_for_height_restriction:
  assumes aaM: "is_struct sig aM"
      and r: "r \<in> world aM"
      and aM : "is_gen_substruct sig aM {r} aM"
      and Mhr:"is_height_restriction sig aM r k M"
      and w: "w \<in> world aM"
      and hw: "height r (ops sig) (rel aM) w \<le> k"
      and Z:"\<And>w1 w2 n.  
            Z n w1 w2 \<equiv> 
            w1 = w2 \<and> w1 \<in> world M \<and>
            height r (ops sig) (rel aM) w1 \<le> k - n"
    shows "n_bisim Z 
           (k - height r (ops sig) (rel aM) w) 
           M aM w w"
proof -
  have MssaM: "world M \<subseteq> world aM" 
    using is_height_restriction_world_subseteq[OF Mhr].
  have waM: "world aM = generated_set (ops sig) (rel aM) {r}"
    using aM by (meson gen_substruct_world)
  have wM: "world M = {w. w \<in> world aM \<and>
                         height r (ops sig) (rel aM) w \<le> k }" 
    using Mhr  by (simp add: is_height_restriction_def)
  have "\<And>i v v'.
     Z i v v' \<Longrightarrow> v \<in> world M \<and> v' \<in> world M"
    using Z by simp
  have "(\<forall>i v v'. 
  i + 1 \<le> k - height r (ops sig) (rel aM) w \<longrightarrow> 
  Z (i + 1) v v' \<longrightarrow> Z i v v')" 
    using Z by auto
  have "(\<forall>v v' p. Z 0 v v' \<longrightarrow> valt M p v = valt aM p v')"
    by (metis (no_types, opaque_lifting) Mhr Z is_height_restriction_valt)
  have "Z (k - height r (ops sig) (rel aM) w) w w"
    unfolding Z
    by (metis (no_types, lifting) Mhr diff_diff_cancel 
       dual_order.refl hw is_height_restriction_def mem_Collect_eq w)
  have 
  "\<forall>i v v' ul m.
        i + 1 \<le> k - height r (ops sig) (rel aM) w \<and> 
        Z (i + 1) v v' \<and> rel M m (v # ul) \<longrightarrow>
        (\<exists>ul'. rel aM m (v' # ul') \<and> 
        (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))"
  proof (safe)
    fix i v v' ul m
    assume i1:"i + 1 \<le> k - height r (ops sig) (rel aM) w"
       and Zi1vv:"Z (i + 1) v v'"
       and rvul: "rel M m (v # ul)"
    then have "v = v'" unfolding Z by simp
    then have aMvul:"rel aM m (v # ul)" 
      by (metis (no_types, lifting) Mhr is_height_restriction_def 
         restrict_rel_def rvul)
    then have m:"m \<in> ops sig" using aM is_struct_def 
      by (metis aaM)
    from Zi1vv Z have v:"v \<in> world M" by blast
    from Zi1vv have hv: "height r (ops sig) (rel aM) v \<le> k - (i + 1)"
      unfolding Z by metis
    have ugs: "\<And>u. u \<in> set ul \<Longrightarrow> u \<in> generated_set (ops sig) (rel aM) {r}"
      using  v waM
      by (metis (mono_tags, lifting) \<open>rel aM m (v # ul)\<close> aM 
    gen_substruct_rel restrict_rel_def set_subset_Cons subsetD)
    have i1lek: "i+1\<le> k" using i1 by simp
    then have "\<And>u. u \<in> set ul \<Longrightarrow>
            height r (ops sig) (rel aM) u \<le> k -i" unfolding Z
    proof -
      fix u assume u:"u \<in> set ul"
      have vgs:"v \<in> generated_set (ops sig) (rel aM) {r}" using v waM
       using MssaM by blast
      then show "height r (ops sig) (rel aM) u \<le> k -i"
        using generated_set_height_add_1 [OF vgs m aMvul u] hv i1lek 
        by linarith
    qed
      then  have "\<forall>u u'. (u, u') \<in> set (zip ul ul) \<longrightarrow> Z i u u'"
      unfolding Z wM 
      using ugs waM zip_same by fastforce
    with aMvul show
    "\<exists>ul'. rel aM m (v' # ul') \<and>
     (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')"
      using \<open>v = v'\<close> by blast
  qed
  have 
  "\<forall>i v v' ul' m.
        i + 1 \<le> k - height r (ops sig) (rel aM) w \<and> 
        Z (i + 1) v v' \<and> rel aM m (v' # ul') \<longrightarrow>
        (\<exists>ul. rel M m (v # ul) \<and> 
    (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))"
  proof (safe)
    fix i v v' ul' m
    assume i1:"i + 1 \<le> k - height r (ops sig) (rel aM) w"
       and Zi1vv:"Z (i + 1) v v'"
       and rv'ul': "rel aM m (v' # ul')"
    then have veqv':"v = v'" unfolding Z by simp
    from Zi1vv Z have v:"v \<in> world M" by blast
    from Zi1vv have hv: "height r (ops sig) (rel aM) v \<le> k - (i + 1)"
      unfolding Z by metis
    from rv'ul' have m:"m \<in> ops sig" using aM is_struct_def 
      by (metis aaM)
    have ugs: "\<And>u. u \<in> set ul' \<Longrightarrow> u \<in> generated_set (ops sig) (rel aM) {r}"
      using  v waM
      by (metis (mono_tags, lifting) \<open>rel aM m (v' # ul')\<close> aM 
    gen_substruct_rel restrict_rel_def set_subset_Cons subsetD)
    have i1lek: "i+1\<le> k" using i1 by simp
    then have "\<And>u. u \<in> set ul' \<Longrightarrow>
            height r (ops sig) (rel aM) u \<le> k -i" unfolding Z
    proof -
      fix u assume u:"u \<in> set ul'"
      have vgs:"v \<in> generated_set (ops sig) (rel aM) {r}" using v waM
       using MssaM by blast
      then show "height r (ops sig) (rel aM) u \<le> k -i"
        using generated_set_height_add_1 [OF vgs m _ u] hv i1lek rv'ul' veqv'
       by simp
   qed
   then have "\<And>u. u \<in> set ul' \<Longrightarrow> u \<in> world M" 
     using wM ugs waM by fastforce
   then have "rel M m (v # ul')" using 
   restrict_rel_def Mhr 
     by (smt (verit, best) is_height_restriction_rel rv'ul' set_ConsD v veqv')
   then show "\<exists>ul. rel M m (v # ul) \<and> 
          (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u')"
     unfolding Z 
     by (meson \<open>\<And>ua. ua \<in> set ul' \<Longrightarrow>
   height r (ops sig) (rel aM) ua \<le> k - i\<close> 
    \<open>\<And>ua. ua \<in> set ul' \<Longrightarrow> ua \<in> world M\<close> zip_same)
 qed
  show ?thesis  unfolding n_bisim_def 
    using MssaM Z \<open>Z (k - height r (ops sig) (rel aM) w) w w\<close> \<open>\<forall>i v v' ul m. i + 1 \<le> k - height r (ops sig) (rel aM) w \<and> Z (i + 1) v v' \<and> rel M m (v # ul) \<longrightarrow> (\<exists>ul'. rel aM m (v' # ul') \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))\<close> \<open>\<forall>i v v' ul' m. i + 1 \<le> k - height r (ops sig) (rel aM) w \<and> Z (i + 1) v v' \<and> rel aM m (v' # ul') \<longrightarrow> (\<exists>ul. rel M m (v # ul) \<and> (\<forall>u u'. (u, u') \<in> set (zip ul ul') \<longrightarrow> Z i u u'))\<close> \<open>\<forall>v v' p. Z 0 v v' \<longrightarrow> valt M p v = valt aM p v'\<close> by auto
qed


inductive nth_world::
 "('m,'p,'a) struct \<Rightarrow>'a \<Rightarrow> 
  ( (('m,'p) cform) set) \<Rightarrow> (('m,'p) cform \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow>
  nat \<Rightarrow> 'a \<Rightarrow> bool"
 for M :: "('m,'p,'a) struct" and r:: 'a
 and s:: "('m,'p) cform set" 
 and cwl :: "('m,'p) cform \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where
   zero : "nth_world M r s cwl 0 r"
 | suc: "nth_world M r s cwl n v \<Longrightarrow> 
         cDIAM m fl \<in> s \<Longrightarrow>
         asatis M v (cDIAM m fl) \<Longrightarrow>
         w \<in> set (cwl (cDIAM m fl) v)
 \<Longrightarrow>  nth_world M r s cwl (n+1) w"

definition nth_worlds ::
 "('m,'p,'a) struct \<Rightarrow>'a \<Rightarrow> 
  (('m,'p) cform) set \<Rightarrow> (('m,'p) cform \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow>
 nat \<Rightarrow>'a set" where
 "nth_worlds M r s cwl n = { w | w. nth_world M r s cwl n w}"

lemma nth_worlds_0:
 "nth_worlds M r s cwl 0 = {r}" 
  unfolding nth_worlds_def set_eq_iff mem_Collect_eq
  by (metis One_nat_def Suc_n_not_le_n le_add2 nth_world.simps singleton_iff)


lemma nth_worlds_step:
  assumes 
  "v \<in> nth_worlds M r s cwl n"
  and "cDIAM m fl \<in> s"
  and "asatis M v (cDIAM m fl)"
  and "w \<in> set (cwl (cDIAM m fl) v)"
shows "w \<in> nth_worlds M r s cwl (n+1)"
  using assms unfolding nth_worlds_def 
  by (metis mem_Collect_eq nth_world.suc)


definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'c "
  where
"uncurry f pair = f (fst pair) (snd pair)"

lemma nth_worlds_suc_subset_image_product:
"(nth_worlds M r s cwl (n+1)) \<subseteq>
 (\<lambda>(v,f,w).w) ` 
((nth_worlds M r s cwl n) \<times> s \<times> 
 \<Union> (set ` ((uncurry cwl) ` (s \<times> (nth_worlds M r s cwl n))) ))"
proof 
(intro subsetI,
 unfold nth_worlds_def mem_Collect_eq)
  fix x 
  assume "\<exists>w. x = w \<and>
             nth_world M r s cwl (n + 1)
              w"
  then obtain w where 
  xw:"x = w" 
  and 
  "nth_world M r s cwl (n + 1) w" by simp 
  then obtain v m fl 
    where
  "nth_world M r s cwl n v"
  and "cDIAM m fl \<in> s"
  and "asatis M v (cDIAM m fl)"
  and "w \<in> set (cwl (cDIAM m fl) v)"
    using nth_world.simps 
    by (metis add_is_0 add_right_imp_eq zero_neq_one)
  then show "x \<in> (\<lambda>(v, f, w). w) `
              ({w |w. nth_world M r s cwl n w} \<times>
               s \<times>
               \<Union> (set `
                   uncurry cwl `
                   (s \<times>
                    {w |w.
                     nth_world M r s cwl n w})))"
    unfolding 
    mem_Sigma_iff mem_Collect_eq uncurry_def 
    Bex_def bex_triv UN_iff 
    apply (auto simp: image_iff )
    using xw by blast
qed


lemma nth_worlds_finite:
  assumes fins: "finite s"
  and "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 (w,f) \<in> set (zip (cwl (cDIAM m fl) v) fl) \<Longrightarrow>
                 asatis M w f"
  and "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
shows "finite (nth_worlds M r s cwl n)" 
proof (induction n)
  case 0
  then show ?case unfolding nth_worlds_0 by simp
next
  case (Suc n)
  then show ?case unfolding Suc_eq_plus1
  proof - 
    from fins Suc have 
    "finite (\<Union> (set `
            uncurry cwl `
            (s \<times> nth_worlds M r s cwl n)))"
      using finite_surj finite_UN finite_set
            finite_cartesian_product 
      by blast
    with fins Suc 
    have 
    "finite( (\<lambda>(v, f, w). w) `
       (nth_worlds M r s cwl n \<times>
        s \<times>
        \<Union> (set `
            uncurry cwl `
            (s \<times> nth_worlds M r s cwl n))))"
   using finite_surj finite_UN finite_set
            finite_cartesian_product 
   by blast
  then show "finite (nth_worlds M r s cwl (n + 1))"
     using nth_worlds_suc_subset_image_product
          [of M r s cwl n] finite_subset
   by blast
qed
qed


definition fin_worlds:: "('m,'p,'a) struct \<Rightarrow>'a \<Rightarrow> 
  (('m,'p) cform) set \<Rightarrow> (('m,'p) cform \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow>
 nat \<Rightarrow> 'a set" where
 "fin_worlds  M r s cwl k = (\<Union>n \<le> k. (nth_worlds M r s cwl n))"

lemma fin_worlds_finite:
  assumes fins: "finite s"
  and "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 (w,f) \<in> set (zip (cwl (cDIAM m fl) v) fl) \<Longrightarrow>
                 asatis M w f"
  and "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
shows "finite (fin_worlds M r s cwl k)" 
  unfolding fin_worlds_def 
proof - 
  have "\<And>n. n \<le> k \<Longrightarrow> finite (nth_worlds M r s cwl n)"
  proof - 
    fix n assume "n \<le> k"
    from nth_worlds_finite[OF fins, of M cwl r n] assms
    show " finite (nth_worlds M r s cwl n)" by blast
  qed
  then show "finite (\<Union> (nth_worlds M r s cwl ` {..k}))"
    by blast
qed


lemma nth_world_fin_worlds: 
  assumes "n \<le> k"
  and "nth_world M r s cwl n w"
shows "w \<in>  fin_worlds M r s cwl k"
  unfolding fin_worlds_def nth_worlds_def
  using assms(1) assms(2) by blast


lemma nth_world_connected_from_root:
  assumes 
   w:"nth_world M r s cwl n w"
 and ss: "(\<Union> (modal_operators ` s)) \<subseteq> \<tau>"
 and cwl_rel: "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
shows
 "(r, w) \<in> (gen_birel \<tau> (rel M))\<^sup>*" using w
proof (induction)
  case zero
  then show ?case by blast 
next
  case (suc n v m fl w)
  then show ?case
  proof - 
    have "m \<in> \<tau>" using ss \<open>cDIAM m fl \<in> s\<close> 
      by (meson SUP_le_iff modal_operators_cDIAM_subseteq)
    have "(v,w) \<in> gen_birel \<tau> (rel M)" 
      using gen_birel_def cwl_rel[OF \<open>cDIAM m fl \<in> s\<close> \<open>asatis M v \<diamondsuit>m fl\<close> ]
            \<open> w \<in> set (cwl (cDIAM m fl) v)\<close> \<open>m \<in> \<tau>\<close> by blast
    then show ?case 
      using suc.IH by auto
  qed
qed



lemma nth_world_subseteq_world:
  assumes 
   r: "r \<in> world M"
  and w:"nth_world M r s cwl n w"
  and "\<And>m fl v. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 set (cwl (cDIAM m fl) v) \<subseteq> world M"
 shows
  "w \<in> world M" using w
proof (induction)
  case zero
  then show ?case using r. 
next
  case (suc n v m fl w)
  then show ?case 
    using assms(3) by blast
qed

lemma fin_worlds_subseteq_world:
  assumes 
   r: "r \<in> world M"
  and "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 set (cwl (cDIAM m fl) v) \<subseteq> world M"
 shows
  "fin_worlds M r s cwl n \<subseteq> world M" 
  unfolding fin_worlds_def nth_worlds_def
  using nth_world_subseteq_world[OF r]
  using assms(2) by auto


lemma nth_world_predecessor:
  assumes 
   w:"nth_world M r s cwl (n+1) w"
  and ss: "rset \<tau> (rel M) \<subseteq> world M"
  and cwl_rel:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
   and ss: "(\<Union> (modal_operators ` s)) \<subseteq> \<tau>"
  and w_not_r:"w \<noteq> r"
shows "\<exists>t' wl m. 
nth_world M r s cwl n t' \<and> w \<in> set wl \<and> 
(\<forall>w0. w0 \<in> set wl \<longrightarrow> nth_world M r s cwl (n+1) w0) \<and> 
m\<in> \<tau> \<and> 
rel M m (t' # wl)
" using w w_not_r
proof -
  from w nth_world.simps
  obtain v :: 'a and m :: 'b and fl :: "('b, 'c) cform list" and vl :: "'a list"
    where
  "w\<noteq> r"
  and a1: "nth_world M r s cwl n v"
  and a2: "cDIAM m fl \<in> s"
  and a3: "v \<in> world M"
  and a4: "w \<in> set (cwl (cDIAM m fl) v)"
  and a5: "length vl = length fl"
  and a6: "rel M m (v # vl)"
  and "\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M x y"
    by (smt (verit, best) add_right_imp_eq asatis.simps(5) w_not_r)
   then have sat: "asatis M v \<diamondsuit>m fl"
    using a6 a5 a3 by auto
  have m:"m \<in> \<tau>" using ss a2 
    by (meson SUP_le_iff modal_operators_cDIAM_subseteq)
  {fix w0 assume w0:"w0 \<in> set (cwl (cDIAM m fl) v)"
    have "nth_world M r s cwl (n + 1) w0"
    using nth_world.suc[OF a1 a2 sat w0].
}
  from a1 a4 this cwl_rel[OF a2 sat] m 
  have 
  "nth_world M r s cwl n v \<and>
       w \<in> set (cwl (cDIAM m fl) v) \<and> 
  (\<forall>w0. w0 \<in> set (cwl (cDIAM m fl) v) \<longrightarrow> nth_world M r s cwl (n + 1) w0) \<and>
  m \<in> \<tau> \<and> rel M m (v # (cwl (cDIAM m fl) v))" 
    by blast
  then show ?thesis by blast
 qed

lemma nth_world_predecessor_exists:
  assumes 
   w:"nth_world M r s cwl (n+1) w"
  and ss: "rset \<tau> (rel M) \<subseteq> world M"
  and cwl_rel:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
   and ss: "(\<Union> (modal_operators ` s)) \<subseteq> \<tau>"
  and w_not_r:"w \<noteq> r"
shows " \<exists>t'. 
nth_world M r s cwl n t' \<and> 
 (t', w) \<in> gen_birel \<tau> (rel M)" using w w_not_r
apply(subst (asm)  nth_world.simps) apply auto (*sledgehammer*)
proof -
  fix v :: 'a and m :: 'b and fl :: "('b, 'c) cform list" and vl :: "'a list"
  assume a1: "nth_world M r s cwl n v"
  assume a2: "cDIAM m fl \<in> s"
  assume a3: "v \<in> world M"
  assume a4: "w \<in> set (cwl (cDIAM m fl) v)"
  assume a5: "length vl = length fl"
  assume a6: "rel M m (v # vl)"
  assume "\<forall>x y. (x, y) \<in> set (zip vl fl) \<longrightarrow> asatis M x y"
  then have "asatis M v (cDIAM m fl)"
    using a6 a5 a3 by auto
  then show ?thesis
    using a4 a2 a1 by (smt (z3) SUP_le_iff case_prodI cwl_rel gen_birel_def mem_Collect_eq modal_operators_cDIAM_subseteq ss)
qed



lemma nth_world_in_tree_predecessor_unique:
 assumes 
   w:"nth_world M r s cwl n w"
  and ss:"rset \<tau> (rel M) \<subseteq> world M"
  and "w \<noteq> r"
  and t1:"(t1, w) \<in> gen_birel \<tau> (rel M)"
  and t2:"(t2, w) \<in> gen_birel \<tau> (rel M)"
  and cwl_ss:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 set (cwl (cDIAM m fl) v) \<subseteq> world M"
  and tree:"tree \<tau> (world M,rel M) r"
shows "t1 = t2" 
proof -
  from tree have r:"r \<in> world M" by (simp add:tree_def)
  have "w \<in> world M" using 
  nth_world_subseteq_world[OF r w  ] cwl_ss by blast
  show ?thesis using tree unfolding tree_ss_alt[OF ss] w
    using \<open>w \<in> world M\<close> assms(2) t1 t2
    using assms(3) by blast
qed


lemma root_in_fin_worlds:
"r \<in> fin_worlds M r s cwl k"
  unfolding fin_worlds_def UN_iff Bex_def 
  nth_worlds_def mem_Collect_eq
  using nth_world.zero
  by (metis atMost_iff bot_nat_0.extremum)

lemma cwl_asatis_ss:
  assumes 
  cwl_len:"length (cwl (cDIAM m fl) v) = length fl"
  and
  cwl_asatis:"\<And>w f.
                 (w,f) \<in> set (zip (cwl (cDIAM m fl) v) fl) \<Longrightarrow>
                 asatis M w f"
shows
  "set (cwl (cDIAM m fl) v) \<subseteq> world M" using assms
proof (intro subsetI)
  fix x assume "x \<in> set (cwl (cDIAM m fl) v)"
  then obtain n where
 x: "x = (cwl (cDIAM m fl) v) ! n"
 and "n < length fl" using cwl_len 
    by (metis in_set_conv_nth)
 
  have "((cwl (cDIAM m fl) v) ! n,fl ! n) \<in> set (zip (cwl (cDIAM m fl) v) fl)"
   using \<open>n < length fl\<close> cwl_len in_set_conv_nth by fastforce
  then show "x \<in> world M" using asatis_in_world
  cwl_asatis x  by metis
qed


lemma nth_world_fin_world: 
  "w \<in>  fin_worlds M r s cwl k  \<equiv>  
  \<exists>n. n \<le> k \<and>
nth_world M r s cwl n w" unfolding fin_worlds_def nth_worlds_def
  by (smt (verit, ccfv_SIG) CollectD CollectI UN_iff atMost_iff)


lemma nth_world_fin_world_cases: 
  "w \<in>  fin_worlds M r s cwl k  \<equiv> w = r \<or>
  (\<exists>n. n + 1 \<le> k \<and>
nth_world M r s cwl (n +1 ) w)" unfolding nth_world_fin_world
using nth_worlds_0
  by (smt (verit, best) less_eq_nat.simps(1) nth_world.simps)


lemma nth_world_connected_from_root':
  fixes M r s cwl k
  assumes 
   w:"nth_world M r s cwl n w"
 and nk:"n \<le> k"
 and ss: "(\<Union> (modal_operators ` s)) \<subseteq> \<tau>"

 and cwl_rel: "\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
defines "W \<equiv> fin_worlds M r s cwl k"
defines "R \<equiv> restrict_rel (rel M) W"
shows
 "(r, w) \<in> (gen_birel \<tau> R)\<^sup>*" using w  nk
proof (induction )
  case zero
  then show ?case by blast 
next
  case (suc n v m fl w)
  then show ?case
  proof - 
    have v:"v \<in> W" unfolding W_def nth_world_fin_world_cases
      by (metis add_leE nth_world.cases suc.hyps(1) suc.prems)
    have "m \<in> \<tau>" using ss \<open>cDIAM m fl \<in> s\<close> 
      by (meson SUP_le_iff modal_operators_cDIAM_subseteq)
    have 
     "set (cwl (cDIAM m fl) v) \<subseteq> (nth_worlds M r s cwl (n+1))"
      using nth_worlds_def nth_world.simps
      by (metis CollectI subsetI suc.hyps(1) suc.hyps(2) suc.hyps(3))
    with cwl_rel[OF \<open>cDIAM m fl \<in> s\<close> \<open>asatis M v \<diamondsuit>m fl\<close> ]
            \<open> w \<in> set (cwl (cDIAM m fl) v)\<close> \<open>m \<in> \<tau>\<close> 
    nth_world_fin_world_cases
    have 
     " restrict_rel (rel M) W m (v # (cwl (cDIAM m fl) v))"
      unfolding  restrict_rel_def W_def using v 
      by (metis (no_types, lifting) W_def nth_world.suc set_ConsD 
            suc.hyps(1) suc.hyps(2) suc.hyps(3) suc.prems)
     
    then have "(v,w) \<in> gen_birel \<tau> R" 
      unfolding gen_birel_def mem_Collect_eq R_def 
      using \<open>m \<in> \<tau>\<close> suc.hyps(4) by blast
     
    then show ?case 
      using suc.IH  suc.prems by auto
    
  qed
qed

lemma nth_worlds_0':
"nth_world M r s cwl 0 t \<equiv> t = r " 
  by (smt (verit, best) Suc_eq_plus1 bot_nat_0.not_eq_extremum nth_world.simps zero_less_Suc)

lemma gen_birel_sub:
  assumes "\<And>m fl. m \<in> \<tau> \<Longrightarrow> R1 m fl \<Longrightarrow> R2 m fl"
  shows "gen_birel \<tau> R1 \<subseteq> gen_birel \<tau> R2"
  unfolding gen_birel_def
  using assms by force

lemma restrict_gen_birel_sub:
  "gen_birel \<tau> (restrict_rel R W) \<subseteq> gen_birel \<tau> R"
  using restrict_rel_def 
  by (metis gen_birel_sub)

lemma restrict_gen_birel_cl_sub:
  "(gen_birel \<tau> (restrict_rel R W))\<^sup>+ \<subseteq> (gen_birel \<tau> R)\<^sup>+"
  using  restrict_gen_birel_sub
  by (metis subsetI trancl_mono)
 

lemma restrict_gen_birel_rcl_sub:
  "(gen_birel \<tau> (restrict_rel R W))\<^sup>* \<subseteq> (gen_birel \<tau> R)\<^sup>*"
  using  restrict_gen_birel_sub
  by (metis rtrancl_mono)


lemma in_gen_birel_in_dom_in_restrict:
  "(w1,w2) \<in> gen_birel \<tau> (restrict_rel R W)\<equiv> 
  (\<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and>w1 \<in> W)"
  using gen_birel_def restrict_rel_def 
proof - 
  {assume
  "(w1,w2) \<in> gen_birel \<tau> (restrict_rel R W)"
  then obtain m ul where 
  "m \<in> \<tau> \<and> (R m (w1 # ul) \<and> (\<forall>x. x \<in> set (w1 # ul) \<longrightarrow> x \<in> W)) \<and> w2 \<in> set ul"
   using gen_birel_def restrict_rel_def 
   by (smt (verit) mem_Collect_eq old.prod.case)
  then have 
  "m \<in> \<tau> \<and> w2 \<in> set ul \<and> R m (w1 # ul) \<and> set ul \<subseteq> W \<and> w1 \<in> W"
    by fastforce
  then have 
  "\<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and>w1 \<in> W"
    by metis
}
  {assume 
  "\<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and>w1 \<in> W"
    then obtain m ul where 
   m: "m \<in> \<tau>" and w2:"w2 \<in> set ul" and w1ul: "R m (w1 # ul)"
   and ss:"set ul \<subseteq> W" and w1: "w1 \<in> W" by blast
    then have 
   "(\<forall>x. x \<in> set (w1 # ul) \<longrightarrow> x \<in> W)" by auto
    with m w1ul w2 have 
  "(w1,w2) \<in> gen_birel \<tau> (restrict_rel R W)"
      unfolding gen_birel_def restrict_rel_def mem_Collect_eq
    by blast
  }
  show 
  " (w1,w2) \<in> gen_birel \<tau> (restrict_rel R W)\<equiv> 
  (\<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and>w1 \<in> W)"
    using \<open>(w1, w2) \<in> gen_birel \<tau> (restrict_rel R W) \<Longrightarrow>
   \<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and> w1 \<in> W\<close> 
  \<open>\<exists>m l. m \<in> \<tau> \<and> w2 \<in> set l \<and> R m (w1 # l) \<and> set l \<subseteq> W \<and> w1 \<in> W \<Longrightarrow>
  (w1, w2) \<in> gen_birel \<tau> (restrict_rel R W)\<close> by argo
qed

lemma tree_nth_worlds_tree:
  fixes M r s cwl k
  assumes tree:" tree \<tau> (world M,rel M) r"
  and ss0:"rset \<tau> (rel M) \<subseteq> world M"
  and cwl_len:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 length (cwl (cDIAM m fl) v) = length fl"
  and cwl_asatis:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 (w,f) \<in> set (zip (cwl (cDIAM m fl) v) fl) \<Longrightarrow>
                 asatis M w f"
  and cwl_rel:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
  and mop:"(\<Union> (modal_operators ` s)) \<subseteq> \<tau>"
defines "W \<equiv> fin_worlds M r s cwl k"
defines "R \<equiv> restrict_rel (rel M) W"
shows "tree \<tau> (W,R) r"
proof-
  from tree have r: "r \<in> world M"
    by (simp add: tree_def)
  have set_cwl_ss_wM:"(\<And>m fl v w f.
        cDIAM m fl \<in> s \<Longrightarrow>
        asatis M v (cDIAM m fl) \<Longrightarrow>
        set (cwl (cDIAM m fl) v) \<subseteq> world M)"
    using cwl_asatis_ss cwl_len cwl_asatis 
    by (meson asatis_in_world in_set_impl_in_set_zip1 subsetI)
  have ss:"rset \<tau> R \<subseteq> W" unfolding W_def R_def 
    by (smt (z3) mem_Collect_eq restrict_rel_def rset_def subsetI)
  have rW:"r \<in> W" unfolding W_def 
    by (simp add: root_in_fin_worlds)
  
  {fix t assume tW: "t \<in> W" and "t \<noteq> r"
    then obtain n where  n1:"nth_world M r s cwl (n+1) t" 
      unfolding W_def fin_worlds_def nth_worlds_def asatis_in_world
  cwl_rel cwl_len
   apply(subst (asm)  nth_world.simps) apply auto
   by (smt (verit, ccfv_threshold) asatis_in_world cwl_asatis cwl_len cwl_rel nth_world.cases)
    then have 
  " (r, t) \<in> (gen_birel \<tau> (rel M))\<^sup>*"
    using nth_world_connected_from_root 
    by (meson assms(2) nth_world_subseteq_world set_cwl_ss_wM tree tree_ss_alt)
}
  have set_cwl_ss_wM:"(\<And>m fl v w f.
        cDIAM m fl \<in> s \<Longrightarrow>
        asatis M v (cDIAM m fl) \<Longrightarrow>
        set (cwl (cDIAM m fl) v) \<subseteq> world M)"
    using cwl_asatis_ss cwl_len cwl_asatis 
    by (meson asatis_in_world in_set_impl_in_set_zip1 subsetI)
  {fix t
  assume "t \<in> fin_worlds M r s cwl k"
  then have "t \<in> world M" 
    using fin_worlds_subseteq_world[OF r]
   set_cwl_ss_wM by auto
  then have "(t, t) \<notin> (gen_birel \<tau> (rel M))\<^sup>+"
    using 
    tree  tree_ss_alt[OF ss0]
    by metis
  then have "(t, t) \<notin> (gen_birel \<tau> R)\<^sup>+" unfolding R_def using restrict_gen_birel_cl_sub
   by blast}

  have set_cwl_ss_wM:"(\<And>m fl v w f.
        cDIAM m fl \<in> s \<Longrightarrow>
        asatis M v (cDIAM m fl) \<Longrightarrow>
        set (cwl (cDIAM m fl) v) \<subseteq> world M)"
    using cwl_asatis_ss cwl_len cwl_asatis 
    by (meson asatis_in_world in_set_impl_in_set_zip1 subsetI)
  {fix t
  assume t:"t \<in> fin_worlds M r s cwl k"
  assume t_ne_r:" t \<noteq> r"
  then obtain n where 
  n1:"nth_world M r s cwl (n+1) t" and "n + 1 \<le> k"
    unfolding fin_worlds_def nth_worlds_def nth_world_fin_world_cases
   by (meson add_leD1 nth_world_fin_world_cases t)
  from t have "t \<in> world M" 
    using fin_worlds_subseteq_world[OF r]
   set_cwl_ss_wM by auto
  obtain t' wl m where 
  " nth_world M r s cwl n t'"
  and 
  "t \<in> set wl"
  and "\<forall>w0. w0 \<in> set wl \<longrightarrow> nth_world M r s cwl (n + 1) w0" 
  and  "m \<in> \<tau>" 
  and "rel M m (t' # wl)"  
    using nth_world_predecessor[OF n1 ss0 _ mop t_ne_r] cwl_rel
    by blast
  then have 
  " set wl \<subseteq> fin_worlds M r s cwl k" using 
  nth_world_fin_world_cases
    by (metis \<open>n + 1 \<le> k\<close> subset_code(1))
  then have t't:"(t', t) \<in> gen_birel \<tau> R" 
    unfolding R_def in_gen_birel_in_dom_in_restrict t W_def
 using nth_world_fin_world_cases 
  by (meson \<open>m \<in> \<tau>\<close> \<open>n + 1 \<le> k\<close> \<open>nth_world M r s cwl n t'\<close> \<open>rel M m (t' # wl)\<close> \<open>t \<in> set wl\<close>
   add_leD1 nth_world_fin_world)
  {fix t1 assume "(t1, t) \<in> gen_birel \<tau> R" 
    then have rM1:"(t1, t) \<in> gen_birel \<tau> (rel M)" using restrict_gen_birel_sub
      R_def  by blast
    have rM2:"(t', t) \<in> gen_birel \<tau> (rel M)" using restrict_gen_birel_sub
      R_def t't by blast
    then have "t1 = t'" 
   using set_cwl_ss_wM
 nth_world_in_tree_predecessor_unique[OF n1 ss0 t_ne_r _ _ _ tree]
  rM1 rM2 by metis
}
  then have "\<exists>!t'. (t', t) \<in> gen_birel \<tau> R" 
    using \<open>(t', t) \<in> gen_birel \<tau> R\<close> by blast}
  show ?thesis unfolding tree_ss_alt[OF ss] unfolding W_def
  proof (safe)
    show " r \<in> fin_worlds M r s cwl k" unfolding nth_world_fin_world_cases
      by blast
    show " \<And>t. t \<in> fin_worlds M r s cwl k \<Longrightarrow> t \<noteq> r \<Longrightarrow> \<exists>t'. (t', t) \<in> gen_birel \<tau> R"
      using \<open>\<And>t. \<lbrakk>t \<in> fin_worlds M r s cwl k; t \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>!t'. (t', t) \<in> gen_birel \<tau> R\<close> by blast
    show "\<And>t. t \<in> fin_worlds M r s cwl k \<Longrightarrow> (t, t) \<in> (gen_birel \<tau> R)\<^sup>+ \<Longrightarrow> False"
      using \<open>\<And>t. t \<in> fin_worlds M r s cwl k \<Longrightarrow> (t, t) \<notin> (gen_birel \<tau> R)\<^sup>+\<close> by blast
    {fix t assume t: "t \<in> fin_worlds M r s cwl k"
      then obtain n where n:"n \<le> k" and 
      nt: "nth_world  M r s cwl n t" unfolding fin_worlds_def
        nth_worlds_def
        by blast
     have 
      rt:"(r, t) \<in> (gen_birel \<tau> (restrict_rel (rel M) (fin_worlds M r s cwl k)))\<^sup>*"
       using  nth_world_connected_from_root'[OF nt n mop] cwl_rel.
      have "(r, t) \<in> (gen_birel \<tau> R)\<^sup>*"
       unfolding R_def W_def using rt.
    }
    then
    show "\<And>t. t \<in> fin_worlds M r s cwl k \<Longrightarrow> (r, t) \<in> (gen_birel \<tau> R)\<^sup>*"
      by blast
    show "\<And>t t' y.
       t \<in> fin_worlds M r s cwl k \<Longrightarrow> t \<noteq> r \<Longrightarrow> (t', t) \<in> gen_birel \<tau> R \<Longrightarrow> 
  (y, t) \<in> gen_birel \<tau> R \<Longrightarrow> t' = y"
   using \<open>\<And>t. \<lbrakk>t \<in> fin_worlds M r s cwl k; t \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>!t'. (t', t) \<in> gen_birel \<tau> R\<close> by blast
qed
qed

lemma height_height_le:
" height_le r \<tau> R w m \<Longrightarrow> height r \<tau> R w = n \<Longrightarrow> height_le r \<tau> R w n"
  unfolding height_def 
  by (metis generated_set_height_height_le height_def height_le_generated_set)

lemma gen_birel_generated_set:
  assumes "(r,w) \<in> (gen_birel \<tau> R)\<^sup>*"
  shows "w \<in> generated_set \<tau> R {r}" using assms
proof (induction rule: rtrancl_induct)
  case base
  then show ?case 
    by (simp add: generated_set.intros(1)) 
next
  case (step w u)
  then show ?case unfolding gen_birel_def mem_Collect_eq using generated_set.intros(2) 
  proof - 
    obtain m ul where 
    "m \<in> \<tau>" and " R m (w # ul)" and "u \<in> set ul" using step  
      by (smt (verit, best) gen_birel_def 
      in_rel_Collect_case_prod_eq in_rel_def)
    with step show ?case 
      by (meson generated_set.intros(2))
qed
qed

lemma generated_set_gen_birel:
  assumes "w \<in> generated_set \<tau> R {r}"
  shows "(r,w) \<in> (gen_birel \<tau> R)\<^sup>*" using assms
proof (induction)
  case (1 x)
  then show ?case by blast
next
  case (2 w m ul u)
  then show ?case 
    by (smt (verit, ccfv_threshold) case_prodI gen_birel_def mem_Collect_eq rtrancl.simps)
qed

lemma generated_set_iff_gen_birel:
 "w \<in> generated_set \<tau> R {r} \<equiv> (r,w) \<in> (gen_birel \<tau> R)\<^sup>*"
  by (smt (verit, ccfv_threshold) gen_birel_generated_set generated_set_gen_birel)

find_theorems"generated_set"

lemma tree_generated_set:
  assumes "tree \<tau> (W,R) r"
  and "rset \<tau> R \<subseteq> W"
  and "w \<in> W"
shows "w \<in> generated_set \<tau> R {r}" 
  using generated_set_iff_gen_birel  assms
  by (metis tree_ss_alt)

lemma root_in_tree:
  assumes t: "tree \<tau> (W,R) r"
  shows "r \<in> W" 
  using t tree_def by fastforce

lemma tree_not_rel_to_root:
  assumes t: "tree \<tau> (W,R) r"
  and ss:"rset \<tau> R \<subseteq> W"
  and t1r:"(t1, r) \<in> gen_birel \<tau> R"
  shows "False"
proof -
  consider (c1) "t1\<noteq> r" | (c2) "t1 = r" 
    by blast
  then
  show "False"
  proof cases
    case c1
    have "t1 \<in> rset \<tau> R" using gen_birel_rset1 
      by (metis t1r)
    then have "(r, t1) \<in> (gen_birel \<tau> R)\<^sup>*" 
      using t unfolding tree_ss_alt[OF ss]
      using ss by auto
    with c1 have "(r, t1) \<in> (gen_birel \<tau> R)\<^sup>+" 
      by (simp add: rtrancl_eq_or_trancl)
    with t1r have " (t1, t1) \<in> (gen_birel \<tau> R)\<^sup>+" by auto
    then show "False" using tree_ss_alt[OF ss] 
      by (meson \<open>t1 \<in> rset \<tau> R\<close> in_mono ss t)
  next
    case c2
    then show ?thesis using tree_ss_alt[OF ss] 
      using rtrancl_into_trancl2 t t1r by blast
  qed
qed


lemma tree_cases:
  assumes t: "tree \<tau> (W,R) r"
  and ss: "rset \<tau> R \<subseteq> W"
  and Wnr:"W \<noteq> {r}"
shows "W = rset \<tau> R"
proof - 
  have "\<And>x. x \<in> W \<Longrightarrow> x \<in> rset \<tau> R" 
  proof - 
    fix x 
    assume "x \<in> W"
    show "x \<in> rset \<tau> R"
    proof -
      consider (c1) "x\<noteq> r" | (c2) "x = r" 
        by blast
      then show "x \<in> rset \<tau> R" using tree_def
      proof cases
        case c1
        assume "x \<noteq> r"
        then show ?thesis using tree_ss_alt[OF ss] gen_birel_def rset_def
         by (metis (no_types, lifting) \<open>x \<in> W\<close> gen_birel_rset2  t)
     next 
       case c2
       assume "x = r"
       then obtain x1 where "x1 \<in> W" and x1ner:"x1 \<noteq> r"
         using Wnr \<open>x \<in> W\<close> by blast
       then have "(r,x1) \<in> (gen_birel \<tau> R)\<^sup>*" 
         using tree_ss_alt[OF ss] c2 
         by (meson generated_set_gen_birel t tree_generated_set)
       then have "(r,x1) \<in> (gen_birel \<tau> R)\<^sup>+"
         using x1ner by (metis rtranclD)
       then obtain x0 where "(r,x0) \<in> gen_birel \<tau> R"
         using tranclD by metis
       then show ?thesis using rset_def gen_birel_def
         by (simp add: c2 gen_birel_rset1)
     qed
   qed
 qed
  then show ?thesis 
    using assms(2) by blast
qed
       
       
lemma tree_not_rel_to_root':
  assumes t: "tree \<tau> (W,R) r"
  and RW:"rset \<tau> R \<subseteq> W"
  and t1r:"(t1, r) \<in> gen_birel \<tau> R"
  shows "False"
proof -
  consider (c1) "W = {r}" | (c2) "W \<noteq> {r}" 
    by blast
  then
  show "False"
  proof cases
    case c1 then show False 
    proof - 
      have "t1 \<in> W" using t1r RW gen_birel_def rset_def
        by (simp add: gen_birel_rset1 in_mono)
      then have "t1 = r" using c1 by blast
      then show ?thesis using t1r 
        by (metis RW c1 empty_iff gen_birel_rset1 subset_singletonD t tree_not_rel_to_root)
    qed
    next
    case c2 then show False
    proof - 
      have "W = rset \<tau> R" using tree_cases c2 t
        by (metis RW)
      then show ?thesis 
        using t tree_not_rel_to_root t1r by fastforce
    qed
  qed
qed


lemma tree_predecessor_unique:
  assumes t:"tree \<tau> (W,R) r"
      and ss:"rset \<tau> R \<subseteq> W"
      and t1:"(t1, w) \<in> gen_birel \<tau> R"
      and t2:"(t2, w) \<in> gen_birel \<tau> R"
    shows "t1 = t2" using t unfolding tree_ss_alt[OF ss]
proof -
  have "w \<noteq> r" using t1  tree_not_rel_to_root t
    using ss by fastforce
  then show ?thesis using t tree_ss_alt[OF ss] 

    by (metis empty_iff gen_birel_rset2 ss subset_singletonD t1 t2 tree_cases)
  
qed


lemma tree_pred_unique_W:
  assumes t:"tree \<tau> (W,R) r"
      and RW:"rset \<tau> R \<subseteq> W"
      and t1:"(t1, w) \<in> gen_birel \<tau> R"
      and t2:"(t2, w) \<in> gen_birel \<tau> R"
    shows "t1 = t2"
proof -
  consider (c1) "W = {r}" | (c2) "W = rset \<tau> R"
    using tree_cases t RW by metis
  then show "t1 = t2" 
  proof cases
    case c1
    then show ?thesis using t1 t2 RW 
      by (metis empty_iff gen_birel_rset2 subset_singletonD t tree_predecessor_unique)
  next
    case c2
    then show ?thesis using tree_predecessor_unique
      by (metis t t1 t2 RW)
  qed
qed

lemma tree_predecessor_unique':
  assumes t:"tree \<tau> (rset \<tau> R,R) r"
      and t1:"R m1 (t1 # wl1)"
      and m1:"m1 \<in> \<tau>"
      and i1:"w \<in> set wl1"
      and t2:"R m2 (t2 # wl2)"
      and m2:"m2 \<in> \<tau>"
      and i2:"w \<in> set wl2"
    shows "t1 = t2" using t unfolding tree_def fst_conv snd_conv
proof -
  have wgb1: "(t1,w) \<in> gen_birel \<tau> R" unfolding gen_birel_def 
    using t1 m1 i1  by blast
  have wgb2: "(t2,w) \<in> gen_birel \<tau> R" unfolding gen_birel_def 
    using t2 m2 i2  by blast
  have "w \<noteq> r" using t1 tree_not_rel_to_root wgb1
    using t by fastforce
  then show ?thesis using t tree_def t1 t2 wgb1 wgb2
    by (simp add: tree_predecessor_unique) 
qed


lemma non_root_height_le_nonzero:
"height_le r \<tau> R w n \<Longrightarrow> w \<noteq> r \<Longrightarrow> n \<noteq> 0" 
  by (metis height_le_root)

lemma root_height_0:
 "height r \<tau> R r = 0"
 by (simp add: cInf_eq_minimum height_def root)


lemma height_le_suc_alt:
"height_le r \<tau> R w (n+1) \<longleftrightarrow> 
 (\<exists>w0. (w0, w) \<in> gen_birel \<tau> R \<and> height_le r \<tau> R w0 n)"
proof (intro iffI)
  assume "height_le r \<tau> R w (n + 1)"
  show "(\<exists>w0. (w0, w) \<in> gen_birel \<tau> R \<and> height_le r \<tau> R w0 n)"
    unfolding gen_birel_def mem_Collect_eq 
    using height_le.simps 
    by (smt (verit, del_insts) \<open>height_le r \<tau> R w (n + 1)\<close> 
add_is_0 add_right_imp_eq case_prodI zero_neq_one)
next 
  assume 
  "\<exists>w0. (w0, w) \<in> gen_birel \<tau> R \<and> height_le r \<tau> R w0 n"
  show "height_le r \<tau> R w (n+1)" unfolding gen_birel_def mem_Collect_eq 
  by (smt (verit) Product_Type.Collect_case_prodD 
 \<open>\<exists>w0. (w0, w) \<in> gen_birel \<tau> R \<and> height_le r \<tau> R w0 n\<close>
 gen_birel_def height_le.intros(2) prod.sel(1) prod.sel(2))
qed

lemma height_le_height_le :
  assumes "height_le r \<tau> R w n"
  shows "height r \<tau> R w \<le> n"
  unfolding height_def using assms 
  by (simp add: wellorder_Inf_le1)


lemma generated_set_height_le_height:
  assumes "w \<in> generated_set \<tau> R {r}"
  shows "height_le r \<tau> R w (height r \<tau> R w)"
  using generated_set_has_height_le 
  by (simp add: assms generated_set_height_height_le)

lemma tree_not_root_trancl:
  assumes "tree \<tau> (W,R) r"
  and "rset \<tau> R \<subseteq> W"
  and "w \<in> W"
  and "w \<noteq> r"
shows "(r, w) \<in> (gen_birel \<tau> R)\<^sup>+"
  using assms
  by (metis generated_set_gen_birel rtranclD tree_generated_set)


lemma tree_has_height:
  assumes t:"tree \<tau> (W,R) r"
  and ss:"rset \<tau> R \<subseteq> W"
   and "w \<in> W"
 shows "\<exists>n. height_le r \<tau> R w n" using
 generated_set_has_height_le tree_generated_set 
  by (metis assms(3) ss t)

lemma tree_height_0_only_root:
  assumes t:"tree \<tau> (W,R) r"
   and ss:"rset \<tau> R \<subseteq> W"
   and w:"w \<in> W"
 shows "height r \<tau> R w  = 0 \<longleftrightarrow> w = r"
proof - 
  from w have "\<exists>n. height_le r \<tau> R w n" 
    using tree_has_height t ss  by metis
  have "height r \<tau> R w = 0 \<Longrightarrow> w = r"
  proof -
    assume "height r \<tau> R w  = 0 "
    then have "height_le r \<tau> R w 0" 
      using height_height_le 
      by (metis \<open>\<exists>n. height_le r \<tau> R w n\<close>)
    then show "w = r" using height_le_root by metis
  qed
  then show ?thesis 
    by (metis root_height_0)
qed


lemma in_rset:
 "w \<in> rset \<tau> R \<equiv> (\<exists>m vl. m \<in> \<tau> \<and> R m vl \<and> w \<in> set vl)"
  unfolding rset_def by auto
  

lemma tree_height_rel_lemma:
  assumes t:"tree Op (W,R) r"
  and RW: "rset Op R \<subseteq> W"
  and w:"w \<in> W"
  and hw:"height r Op R w = hw" 
  and m:"m \<in> Op"
  and rwvl:"R m (w # vl)"
  and v:"v \<in> set vl"
shows "height r Op R v = hw + 1"
proof (rule ccontr)
  have vW:"v \<in> W" using rwvl RW
    by (metis (no_types, lifting) in_mono in_rset
      list.set_intros(2) m v)
  have vner: "v \<noteq> r" using tree_not_rel_to_root' m v rwvl
    using RW gen_birel_def t by fastforce
  with rwvl v vW tree_height_0_only_root[OF t RW vW]
  have hvne0: "height r Op R v \<noteq> 0"  by auto
  from hw rwvl m v have hvle: "height r Op R v \<le> hw + 1" 
    using  RW
    by (metis generated_set_height_add_1 t tree_generated_set w)
  assume "height r Op R v \<noteq> hw + 1"
  with hvne0 hvle have hvlt:"height r Op R v < hw + 1" by fastforce
  from hvne0 obtain n where hv: "height r Op R v = n + 1"
    by (metis Suc_eq_plus1 old.nat.exhaust)
  with hvlt have nhw: "n < hw" by simp
  have 1: "\<not> height_le r Op R w n" 
  proof (rule ccontr)
    assume "\<not> \<not> height_le r Op R w n"
    then have h : "height_le r Op R w n" by metis
    then have "hw \<le> n" 
      using height_le_height_le hw by metis
    then show False using nhw by simp
  qed
  have 2:"height_le r Op R w n"
  proof - 
    have "v \<in> generated_set Op R {r}" 
      using tree_generated_set RW t vW by metis
    then have "height_le r Op R v (n + 1)"
      using generated_set_height_le_height
      by (metis hv)
    then have 
    "(\<exists>w m vl.
        height_le r Op R w n \<and>
        m \<in> Op \<and> R m (w # vl) \<and> v \<in> set vl)"
      using height_le.cases by fastforce
    then
    obtain m0 w0 vl0 where
    "m0 \<in> Op" and "R m0 (w0 # vl0)" 
    and "v \<in> set vl0" and 
    hw0: "height_le r Op R w0 n" 
      by blast
    then have "w0 = w" using tree_pred_unique_W[OF t RW]
     gen_birel_def using m rwvl v by blast
    then show ?thesis using hw0 
      by meson
  qed
  show "False" using 1 2 by metis
qed

lemma n_worlds_height:
  assumes wnw:"nth_world M r s cwl n w"
  and cwl_rel:"\<And>m fl v w f. cDIAM m fl \<in> s \<Longrightarrow> 
                 asatis M v (cDIAM m fl) \<Longrightarrow>
                 rel M m (v # (cwl (cDIAM m fl) v))"
  and ms: "\<And>m fl. cDIAM m fl \<in> s \<Longrightarrow> m \<in> \<tau>"
  and t:"tree \<tau> (world M,rel M) r"
  and rrw: "rset \<tau> (rel M) \<subseteq> world M"
  shows "height r \<tau> (rel M) w = n"
  using wnw
proof (induction rule: nth_world.induct)
  case zero
  then show ?case using root_height_0.
next
  case (suc n v m fl w)
  then have vM:"v \<in> world M" using asatis_in_world
    \<open>asatis M v \<diamondsuit>m fl\<close>  by fastforce
  have mtau:"m \<in> \<tau>" using ms suc by metis
  then show ?case 
    using tree_height_rel_lemma[OF t rrw vM
   \<open>height r \<tau> (rel M) v = n\<close> mtau] 
   cwl_rel[OF \<open>cDIAM m fl \<in> s\<close>]
  
    using suc.hyps(3) suc.hyps(4) by blast
qed

end

