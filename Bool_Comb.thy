(* Title:        Part of the Modal Model Theory project
 * Content:      Serve to prove proposition 2.29 from Blackburn et al. 
                 define and prove properties of Boolean combination
                 prove the boolean combination from a 
                 finite-up-to-equivalence set of formulas is 
                 finite up to equivalence
 *)

theory Bool_Comb
  imports Main Modal_Syntax Modal_Model Modal_Semantics 
  HOL.Equiv_Relations "HOL-Library.FuncSet" Partition_Alt
begin

inductive bool_comb :: "('m,'p) cform set \<Rightarrow> ('m,'p) cform \<Rightarrow> bool" 
  for s :: " ('m,'p) cform set " where
  "bool_comb s cFALSE"
| "f \<in> s \<Longrightarrow> bool_comb s f"
| "bool_comb s f \<Longrightarrow> bool_comb s (cNOT f)"
| "bool_comb s f1 \<Longrightarrow> bool_comb s f2 \<Longrightarrow> bool_comb s (cDISJ f1 f2)"

lemma bool_comb_prop_cform_EXISTS_base:
  assumes "bool_comb {} phi" 
  shows "\<exists>phi0. prop_cform phi0 \<and> 
                  prop_letters phi0 = {} \<and>
           subst \<sigma> phi0 = phi" using assms
proof (induction rule: bool_comb.induct[of "{}"])
  case 1
  then show ?case 
    using prop_cform.intros(1) prop_letters.simps(1) subst.simps(1) by blast
next
  case (2 f)
  then show ?case by simp
next
  case (3 f)
  then show ?case
    by (metis prop_cform.intros(3) 
    prop_letters.simps(4) subst.simps(4)) 
next
  case (4 f1 f2)
  then show ?case
    by (metis Un_empty prop_cform.intros(4) 
       prop_letters.simps(3) subst.simps(3)) 
qed
 
lemma bool_comb_prop_cform_EXISTS_step:
  assumes F:"finite F"
      and x: "x \<notin> F"
      and IH: "\<And> phi . bool_comb F phi \<Longrightarrow>
               (\<exists>phi0.
                   prop_cform phi0 \<and>
                   prop_letters phi0
                   \<subseteq> {n. n < (card F)} \<and>
                   subst \<sigma> phi0 = phi)"
     and ss1:"\<And>x. x < card F \<Longrightarrow> \<sigma>1 x = \<sigma> x"
     and cx:"\<sigma>1 (card F) = x"
   shows "bool_comb (insert x F) phi \<Longrightarrow>
                      (\<exists>phi0.
                          prop_cform phi0 \<and>
                          prop_letters phi0
                          \<subseteq> 
   {n. n< (card (insert x F))} \<and>
                          subst \<sigma>1 phi0 = phi)"
 
proof (induction rule : bool_comb.induct)
  case 1
  then show ?case 
    using prop_cform.intros(1) by auto 
next
  case (2 f)
  then
  consider 
    (c1) "f = x" | (c2) "f \<in> F" by blast
  have
  c1:"f = x \<Longrightarrow> prop_cform (cVAR (card F)) \<and>
       prop_letters (cVAR (card F))
       \<subseteq> {n. n< (card (insert x F))} \<and>
       subst \<sigma>1 (cVAR (card F)) = f"
    using 
   prop_cform.intros(2)
   F x ss1 cx by force
  from IH subst_prop_letters
  have "f \<in> F \<Longrightarrow> \<exists>phi0.
       prop_cform phi0 \<and>
       prop_letters phi0
       \<subseteq> {n. n < card (insert x F)} \<and>
       subst \<sigma>1 phi0 = f" 
  proof - 
    assume "f \<in> F"
    then have bcf:"bool_comb F f" using bool_comb.intros by auto
    then obtain phi0 where
    pfp:"prop_cform phi0"
    and "prop_letters phi0 \<subseteq> {n. n < card F}" 
    and "subst \<sigma> phi0 = f" using IH[OF bcf] by blast
    then have "prop_letters phi0 \<subseteq> {n. n < card (insert x F)}"
      using F x by auto
    have "subst \<sigma>1 phi0 = subst \<sigma> phi0" 
      using subst_prop_letters
      by (smt (verit, ccfv_SIG) \<open>prop_letters phi0 \<subseteq> {n. n < card F}\<close> mem_Collect_eq ss1)
    then show ?case 
      using \<open>prop_letters phi0 \<subseteq> {n. n < card (insert x F)}\<close>
 \<open>subst \<sigma> phi0 = f\<close> pfp by blast
  qed
  with c1 show ?case 
    using \<open>\<And>thesis. \<lbrakk>f = x \<Longrightarrow> thesis; f \<in> F \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> by blast
next
  case (3 f)
  then obtain phi0 where 
   "prop_cform phi0"
   and "prop_letters phi0
       \<subseteq> {n. n < card (insert x F)}"
  and "subst \<sigma>1 phi0 = f" by blast
  then have 
  "prop_cform (cNOT phi0) \<and>
   prop_letters (cNOT phi0) \<subseteq> 
    {n. n < card (insert x F)} \<and>
   subst \<sigma>1 (cNOT phi0) = cNOT f" 
    by (simp add: prop_cform.intros(3))
  then show ?case by blast
next
  case (4 f1 f2)
  then obtain phi1 phi2 where
  "prop_cform phi1 \<and>
       prop_letters phi1
       \<subseteq> {n. n < card (insert x F)} \<and>
       subst \<sigma>1 phi1 = f1" and 
  "prop_cform phi2 \<and>
       prop_letters phi2
       \<subseteq> {n. n < card (insert x F)} \<and>
       subst \<sigma>1 phi2 = f2 " 
    by blast
  then have 
  "prop_cform (cDISJ phi1 phi2) \<and>
       prop_letters (cDISJ phi1 phi2)
       \<subseteq> {n. n < card (insert x F)} \<and>
       subst \<sigma>1 (cDISJ phi1 phi2) = cDISJ f1 f2"
    using prop_cform.simps prop_letters.simps
   subst.simps prop_cform.intros
    by auto
  then show ?case by blast
qed

lemma bool_comb_prop_cform_EXISTS:
  assumes fs:"finite fs"
  shows "\<exists>\<sigma>. 
         \<forall>phi. bool_comb fs phi \<longrightarrow>
          (\<exists>phi0. prop_cform phi0 \<and> 
                  prop_letters phi0 \<subseteq> {n. n < card fs} \<and>
           subst \<sigma> phi0 = phi)" using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case using 
  bool_comb_prop_cform_EXISTS_base
    by (metis empty_subsetI)
next
  case (insert x F)
  obtain \<sigma> where
  3:"\<And>phi. bool_comb F phi \<Longrightarrow>
               (\<exists>phi0.
                   prop_cform phi0 \<and>
                   prop_letters phi0
                   \<subseteq> {n. n < card F} \<and>
                   subst \<sigma> phi0 = phi)"
    using insert.IH by blast
  define \<sigma>1 where
  "\<sigma>1 \<equiv> \<lambda>a. if a < card F then \<sigma> a else x"
  have s1:"\<And>x. x < card F \<Longrightarrow> \<sigma>1 x = \<sigma> x"
  using \<sigma>1_def by presburger
  have s1':"\<sigma>1 (card F) = x" using \<sigma>1_def by presburger
  show ?case 
    using 
  bool_comb_prop_cform_EXISTS_step[OF insert(1) insert(2) 3]
   by (metis \<sigma>1_def s1')
  
qed

function peval :: "('p \<Rightarrow> bool) \<Rightarrow> ('m,'p) cform \<Rightarrow> bool" where 
  "peval \<sigma> (cVAR p) = \<sigma> p"
| "peval \<sigma> (cDISJ f1 f2) = (peval \<sigma> f1 \<or> peval \<sigma> f2)"
| "peval \<sigma> cFALSE = False"
| "peval \<sigma> (cNOT f) = (\<not> peval \<sigma> f)"
| "peval \<sigma> (cDIAM m fl) = False"
proof -
  show "\<And>P x. (\<And>\<sigma> p. x = (\<sigma>, cVAR p) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<sigma> f1 f2. x = (\<sigma>, cDISJ f1 f2) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<sigma>. x = (\<sigma>, cFALSE) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>\<sigma> f. x = (\<sigma>, cNOT f) \<Longrightarrow> P) \<Longrightarrow> 
 (\<And>\<sigma> m fl. x = (\<sigma>, \<diamondsuit>m fl) \<Longrightarrow> P) \<Longrightarrow> P"
    by (metis old.prod.exhaust prop_letters.cases)
qed auto
termination
 by (relation \<open>{((c,d),g,h). size d < size h}\<close>)
 (auto simp: subst_termination_helper wf_size_subst)


lemma peval_prop_letters:
  assumes plf:"prop_letters phi \<subseteq> s"
      and f12: "\<And>p. p \<in> s \<Longrightarrow> f1 p = f2 p"
    shows "peval f1 phi = peval f2 phi" using assms
proof (induction phi rule:cform.induct)
qed auto


lemma peval_asatis:
  assumes "prop_cform f"
      and "w \<in> world M"
      and "\<And>p. p \<in> prop_letters f \<Longrightarrow> \<sigma> p = valt M p w"
    shows "asatis M w f \<equiv> peval \<sigma> f" using assms
proof (induction f)
qed auto



lemma subst_prop_cform_asatis:
  assumes "subst \<sigma> phi0 = phi"
      and "prop_cform phi0"
      and "w \<in> world M"
      and "\<And>p. p \<in> prop_letters phi0 \<Longrightarrow> v p = asatis M w (\<sigma> p)"
    shows "asatis M w phi =
           peval v phi0" using assms
proof (induction phi arbitrary : phi0 rule:cform.induct)
  case (cVAR x)
  from \<open>subst \<sigma> phi0 = cVAR x\<close> 
  obtain m where "phi0 = cVAR m" and "\<sigma> m = cVAR x"
    using cVAR.prems(2) prop_cform.cases by force
  then show ?case
    by (simp add: cVAR.prems(4))
next
  case cFALSE
  then show ?case using peval.elims(2) by force 
next
  case (cDISJ phi1 phi2)
  consider 
  (c1) "!p. cVAR p \<noteq> phi0" | (c2) "\<exists>p. cVAR p = phi0"
    by metis
  then show ?case
  proof (cases)
    case c1
    from c1 obtain phi01 phi02 where 
      "phi0 = cDISJ phi01 phi02 \<and>
            subst \<sigma> phi01 = phi1 \<and> subst \<sigma> phi02 = phi2"
      using subst_cDISJ \<open>subst \<sigma> phi0 = cDISJ phi1 phi2\<close> 
      by blast
    then show ?thesis 
      by (metis UnCI c1 cDISJ.IH(1) cDISJ.IH(2) cDISJ.prems(2) 
   cDISJ.prems(3) cDISJ.prems(4) cform.distinct(15) cform.distinct(9)
 cform.inject(2) asatis.simps(3) peval.simps(2) prop_cform.simps
 prop_letters.simps(3))
  next
    case c2 
    then show ?thesis 
      using cDISJ.prems(1) cDISJ.prems(4) by force
  qed
next
  case (cNOT phi)
  consider 
  (c1) "!p. cVAR p \<noteq> phi0" | (c2) "\<exists>p. cVAR p = phi0"
    by metis
  then show ?case
  proof (cases)
    case c1
    from c1 obtain phi00 where 
      "phi0 = cNOT phi00 \<and>
            subst \<sigma> phi00 = phi"
      using subst_cNOT \<open>subst \<sigma> phi0 = cNOT phi\<close> 
      by blast
    then show ?thesis 
      by (metis c1 cNOT.IH cNOT.prems(2) cNOT.prems(3) cNOT.prems(4) 
cform.distinct(11) cform.distinct(15) cform.inject(3) asatis.simps(4) 
peval.simps(4) prop_cform.simps prop_letters.simps(4))
  next
    case c2 
    then show ?thesis 
      using cNOT by force
  qed
next
  case (cDIAM x1a x2)
  then show ?case
    by (smt (verit, best) cform.distinct(17) cform.distinct(19)
 cform.distinct(7) cform.simps(18) peval.simps(1) prop_cform.simps
 prop_letters.simps(2) singletonI subst.elims)
qed



lemma subst_equiv:
  assumes p1:"prop_cform (phi1::('m,'q) cform)"
      and p2:"prop_cform phi2"
      and eq12:"cequiv (TYPE ('a)) phi1 phi2"
    shows "cequiv (TYPE ('a)) (subst (\<sigma>::'q \<Rightarrow> ('m, 'p) cform) phi1) (subst \<sigma> phi2)"
  unfolding cequiv_def
proof (intro allI impI)
  fix "M"::"('m,'p,'a) struct" 
  fix w :: "'a"
   consider 
  (c1) "w \<in> world M" | (c2) "w \<notin> world M" by blast
   then show "asatis M w (subst \<sigma> phi1) = asatis M w (subst \<sigma> phi2)"
   proof (cases)
     case c1
      define v where 
   "v \<equiv> \<lambda>p w. asatis M w (\<sigma> p)"
  then have 
  v: "\<And>w p. v p w \<Longrightarrow> w \<in> world M" 
    using asatis_in_world v_def  by metis
  obtain M' where
  wM':" world M' = world M" and rM':" rel M' = rel M"
  and vM' : "valt M' = v" by force
    have ppl:"\<And>p.(\<lambda>p. valt M' p w) p = (\<lambda>p. asatis M w (\<sigma> p)) p"
    using vM' v_def by presburger
  have c12:"\<And>(M::('m,'q,'a) struct) w.
        asatis M w phi1 \<equiv> asatis M w phi2"
    using eq12 unfolding cequiv_def by presburger

  moreover have "asatis M w (subst \<sigma> phi1) \<equiv> 
       peval (\<lambda>p. asatis M w (\<sigma> p)) phi1" 
  using subst_prop_cform_asatis
  by (smt (verit, ccfv_threshold) assms(1) c1) 
  moreover have "asatis M w (subst \<sigma> phi2) \<equiv> 
       peval (\<lambda>p. asatis M w (\<sigma> p)) phi2" 
  using subst_prop_cform_asatis
  by (smt (verit, ccfv_threshold) assms(2) c1)
  moreover have "asatis M' w phi1 \<equiv> peval (\<lambda>p. valt M' p w) phi1"
  using peval_asatis
  by (simp add: assms(3) c1 p1 peval_asatis wM')
  
  moreover have "asatis M' w phi2 \<equiv> peval (\<lambda>p. valt M' p w) phi2"
  using peval_asatis
  by (simp add:  c1 p2 peval_asatis wM')
  
  moreover have "asatis  M' w phi1 \<equiv> asatis M' w phi2"
    using c12 by auto 

  moreover have "peval (\<lambda>p. valt M' p w) phi1 \<equiv>
        peval (\<lambda>p. asatis M w (\<sigma> p)) phi1" 
    using peval_prop_letters ppl 
    by auto
  moreover 
  have "peval (\<lambda>p. valt M' p w) phi2 \<equiv>
        peval (\<lambda>p. asatis M w (\<sigma> p)) phi2" 
    using peval_prop_letters ppl by auto

  ultimately show ?thesis 
    using \<open>asatis M' w phi1 \<equiv> asatis M' w phi2\<close> by blast
 next
     case c2
     then show ?thesis using asatis_in_world by metis
   qed
 qed



lemma bool_comb_INJ_prop_cform_cequiv:
  assumes 
  sk:"\<And>\<phi>:: ('m,'p) cform. \<phi> \<in> C \<Longrightarrow>
      subst \<sigma> (sk \<phi>) = \<phi> \<and> prop_cform (sk \<phi>) \<and>
      prop_letters  (sk \<phi>) \<subseteq> s" 
  and 
  r:"\<And> \<phi>s. \<phi>s \<in> (C //cequiv_on TYPE('a) C) \<Longrightarrow>
         r \<phi>s \<in> \<phi>s"
shows "inj_on 
      (\<lambda> \<phi>s. 
     
       {v. peval v (sk (r \<phi>s)) \<and> (\<forall>q. v q \<longrightarrow> q \<in> s)} )
      (C //cequiv_on TYPE('a) C)" unfolding inj_on_def
proof (intro ballI impI)
  fix x y
  assume 
      x:"x \<in> C // cequiv_on TYPE('a) C"
  and y:"y \<in> C // cequiv_on TYPE('a) C"
  and seteq:"{v. peval v (sk (r x)) \<and> (\<forall>q. v q \<longrightarrow> q \<in> s)} =
       {v. peval v (sk (r y)) \<and> (\<forall>q. v q \<longrightarrow> q \<in> s)}"
  have eq:"equiv C (cequiv_on TYPE('a) C)"
    using cequiv_relation_equiv by blast
  define rx where "rx = r x"
  define ry where "ry = r y"
  have rx:"rx \<in> x" using x r rx_def by simp
  have ry:"ry \<in> y" using y r ry_def by simp
  have "rx \<in> C" using x r rx_def
    using in_quotient_imp_subset eq by blast
  have "ry \<in> C" using y r ry_def
    using in_quotient_imp_subset eq by blast
  define rpx where "rpx = sk rx"
  define rpy where "rpy = sk ry"
  have sx:"subst \<sigma> rpx = rx" using rpx_def sk using \<open>rx \<in> C\<close> by auto
  have px:"prop_cform rpx" using rpx_def sk using \<open>rx \<in> C\<close> by auto
  have lx:"prop_letters rpx \<subseteq> s" using rpx_def sk using \<open>rx \<in> C\<close> by auto
  have sy:"subst \<sigma> rpy = ry" using rpy_def sk using \<open>ry \<in> C\<close> by auto
  have py:"prop_cform rpy" using rpy_def sk using \<open>ry \<in> C\<close> by auto
  have ly:"prop_letters rpy \<subseteq> s" using rpy_def sk using \<open>ry \<in> C\<close> by auto
  have eqpxy:"cequiv TYPE('a) rpx rpy" unfolding cequiv_def
  proof (intro allI)
    fix "M"
    fix w :: "'a"
    have "w \<in> world M \<Longrightarrow> asatis M w rpx = asatis M w rpy"
    proof -
      assume "w \<in> world M" 
      define M1 where "M1 = (world M,rel M,\<lambda> q w. if q \<in> s then valt M q w else False)"
      then have
      "world M1 = world M" by simp 
      have "rel M1 = rel M" using M1_def by simp
      have v1: "valt M1 = (\<lambda> q w. if q \<in> s then valt M q w else False)"
      using M1_def by simp
      have 1:"asatis M1 w rpx = asatis M w rpx"
        using  asatis_prop_letters lx v1 
        by (smt (verit, del_insts) \<open>rel M1 = rel M\<close>
           \<open>w \<in> world M\<close> \<open>world M1 = world M\<close> subsetD)
      have 2:"asatis M1 w rpy = asatis M w rpy"
        using  asatis_prop_letters ly v1 
        by (smt (verit, del_insts) \<open>rel M1 = rel M\<close> 
            \<open>w \<in> world M\<close> \<open>world M1 = world M\<close> subsetD)
      have 3:"asatis M1 w rpx = peval (\<lambda>p. valt M1 p w) rpx" 
         using peval_asatis  v1
         by (metis (no_types, lifting) \<open>w \<in> world M\<close> \<open>world M1 = world M\<close> px)
       have 4:"asatis M1 w rpy = peval (\<lambda>p. valt M1 p w) rpy" 
          using peval_asatis  v1
          by (metis (no_types, lifting) \<open>w \<in> world M\<close> \<open>world M1 = world M\<close> py)
      have "(\<lambda>p. valt M1 p w) \<in> 
            {v. peval v rpx \<and> (\<forall>q. v q \<longrightarrow> q \<in> s)} \<equiv>
            (\<lambda>p. valt M1 p w) \<in> 
            {v. peval v rpy \<and> (\<forall>q. v q \<longrightarrow> q \<in> s)}"
        using seteq rx_def ry_def rpx_def rpy_def
        by presburger
      then show ?thesis 
        using "1" "2" "3" "4" v1 by fastforce
    qed
    then show "asatis M w rpx = asatis M w rpy" 
      using asatis_in_world by metis
  qed
  have "cequiv TYPE('a) rx ry"
    using subst_equiv[OF px py] sx sy eqpxy by blast
  have rxry:"(rx, ry) \<in> cequiv_on TYPE('a) C"
    using subst_equiv cequiv_cequiv_on 
    using \<open>cequiv TYPE('a) rx ry\<close> \<open>rx \<in> C\<close> \<open>ry \<in> C\<close> by blast
  show "x = y"
  proof (rule quotient_eqI[of C "cequiv_on TYPE('a) C" 
         "x" "y" "rx" "ry"])
    show "equiv C (cequiv_on TYPE('a) C)" using eq.
    show "x \<in> C // cequiv_on TYPE('a) C" using x.
    show "y \<in> C // cequiv_on TYPE('a) C" using y.
    show "rx \<in> x" using rx.
    show "ry \<in> y" using ry.
    show "(rx, ry) \<in> cequiv_on TYPE('a) C" using rxry.
  qed
qed


definition bool_combs :: "('m,'p) cform set \<Rightarrow> ('m,'p) cform set " where
"bool_combs fs = {f . bool_comb fs f}"


lemma finite_valuation_set :
  assumes s: "finite s"
  shows "finite {vs | vs. \<forall>v q. v \<in> vs \<longrightarrow> v q --> q  \<in> s} "
proof -
  have fpp:"finite (Pow (Pow s))" using finite_Pow_iff s by blast
  have inj:"inj (\<lambda>vs. Collect ` vs)"
  proof -
    obtain PP :: "(('b \<Rightarrow> bool) set \<Rightarrow> 'b set set) \<Rightarrow> ('b \<Rightarrow> bool) set" and PPa :: "(('b \<Rightarrow> bool) set \<Rightarrow> 'b set set) \<Rightarrow> ('b \<Rightarrow> bool) set" and PPb :: "(('b \<Rightarrow> bool) set \<Rightarrow> 'b set set) \<Rightarrow> ('b \<Rightarrow> bool) set" and PPc :: "(('b \<Rightarrow> bool) set \<Rightarrow> 'b set set) \<Rightarrow> ('b \<Rightarrow> bool) set" where
      f1: "\<forall>f. PP f \<noteq> PPa f \<and> f (PP f) = f (PPa f) \<or> inj f"
      by (metis (no_types) injI)
    obtain bb :: "(('b \<Rightarrow> bool) \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> bool" and bba :: "(('b \<Rightarrow> bool) \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> bool" and bbb :: "(('b \<Rightarrow> bool) \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> bool" and bbc :: "(('b \<Rightarrow> bool) \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> bool" where
      f2: "\<forall>f. bb f \<noteq> bba f \<and> f (bb f) = f (bba f) \<or> inj f"
      by (metis (no_types) injI)
    have "(\<exists>b. bba Collect b \<noteq> bb Collect b) \<or> bba Collect = bb Collect"
      by blast
    then show ?thesis
      using f2 f1 by (metis (no_types) inj_image_eq_iff mem_Collect_eq)
  qed
  have "{vs | vs. \<forall>v q. v \<in> vs \<longrightarrow> v q --> q  \<in> s} = 
        {vs. (\<lambda>vs. Collect ` vs) vs  \<in> (Pow (Pow s))}"
   by auto
  then show ?thesis using finite_inverse_image[OF fpp inj]
    by presburger
qed

lemma bool_comb_INJ_prop_cform_cequiv_choice:
  assumes "finite (fs:: ('m,'p) cform set)"
  shows "finite (bool_combs fs //cequiv_on TYPE('a) (bool_combs fs))"
proof -
  define C where "C = bool_combs fs"
  obtain \<sigma> where 
  sigma: "\<forall>phi. bool_comb fs phi \<longrightarrow>
         (\<exists>phi0. prop_cform phi0 \<and> 
           prop_letters phi0 \<subseteq> {n. n < card fs} \<and> 
           subst \<sigma> phi0 = phi)" using bool_comb_prop_cform_EXISTS
    using assms by blast
  obtain sk where
  sk:"(\<And>\<phi>. \<phi> \<in> C \<Longrightarrow> subst \<sigma> (sk \<phi>) = \<phi> 
  \<and> prop_cform (sk \<phi>) \<and> 
  prop_letters (sk \<phi>) \<subseteq>  {n. n < card fs})"
    using choice C_def bool_combs_def
    by (metis mem_Collect_eq sigma) 
  obtain r where
  r:"(\<And>\<phi>s. \<phi>s \<in> C // cequiv_on TYPE('a) C \<Longrightarrow> r \<phi>s \<in> \<phi>s)"
    using C_def cequiv_equiv
    by (metis all_not_in_conv cequiv_relation_equiv 
       in_quotient_imp_non_empty)
  have i: "inj_on 
      (\<lambda> \<phi>s. 
     
       {v. peval v (sk (r \<phi>s)) \<and> (\<forall>q. v q \<longrightarrow> q \<in> {n. n < card fs})} )
      (bool_combs fs //cequiv_on TYPE('a) (bool_combs fs))"
    using
 bool_comb_INJ_prop_cform_cequiv[OF sk r]
    using C_def by blast
  have fin:"finite {vs | vs. \<forall>v q. v \<in> vs \<longrightarrow> v q --> q  \<in> {n. n < card fs}} "
    using finite_valuation_set by blast
  have ss: "(\<lambda>\<phi>s. {v. peval v (sk (r \<phi>s)) \<and>
   (\<forall>q. v q \<longrightarrow> q \<in> {n. n < card fs})}) `
  bool_combs fs // cequiv_on TYPE('a) (bool_combs fs)
  \<subseteq> {vs |vs. \<forall>v q. v \<in> vs \<longrightarrow> v q \<longrightarrow> q \<in> {n. n < card fs}}"
   by blast
  show "finite (bool_combs fs //cequiv_on TYPE('a) (bool_combs fs))"
    using inj_on_finite[OF i ss fin].
qed


lemma bool_comb_cDIAM:
 "bool_comb s (cDIAM m fl) \<equiv> (cDIAM m fl) \<in> s" 
  by (smt (verit, best) bool_comb.simps cform.distinct(13) cform.distinct(17) cform.simps(24))


lemma bool_comb_cVAR:
 "bool_comb s (cVAR p) \<equiv> (cVAR p) \<in> s" 
  by (smt (verit, ccfv_SIG) bool_comb.simps cform.distinct(1) 
      cform.distinct(3) cform.distinct(5))


lemma bool_comb_prop_cform: 
 "(prop_cform f \<and> prop_letters f \<subseteq> s) \<equiv> bool_comb (cVAR ` s) f"
proof (induction f)
  case (cVAR x)
  then show ?case 
    using bool_comb_cVAR prop_cform.intros(2) by fastforce
next
  case cFALSE
  then show ?case 
    by (simp add: bool_comb.intros(1) prop_cform.intros(1))
next
  case (cDISJ f1 f2)
  then show ?case
    by (smt (verit, ccfv_threshold) Un_subset_iff 
bool_comb.simps cform.distinct(3) cform.inject(2) cform.simps(14)
 cform.simps(20) deg.simps(4) deg_0_propform f_inv_into_f 
max_nat.eq_neutr_iff prop_letters.simps(3))
next
  case (cNOT f)
  then show ?case 
    by (metis (no_types, lifting) bool_comb.simps cform.inject(3) 
cform.simps(10) cform.simps(16) cform.simps(20) deg.simps(3) 
deg_0_propform f_inv_into_f prop_letters.simps(4))
next
  case (cDIAM x1a x2)
  then show ?case 
    by (meson bool_comb_cDIAM cform.distinct(8) cform.simps(18)
 cform.simps(22) cform.simps(24) imageE prop_cform.cases)
qed


lemma bool_comb_rep_cequiv0:
  assumes r:"\<And>a. a \<in> A \<Longrightarrow> \<exists>b. b \<in> B \<and> cequiv TYPE('a) a b"
  and f:"bool_comb A f"
shows "\<exists>f0. bool_comb B f0 \<and> cequiv TYPE('a) f f0" using f r
proof (induction f rule: bool_comb.induct)
  case 1
  then show ?case 
    using bool_comb.intros(1) cequiv_def by blast 
next
  case (2 f)
  then show ?case 
    using bool_comb.intros(2) by blast
next
  case (3 f)                                                
  then show ?case using cequiv_cNOT_cong 
    using bool_comb.intros(3) by blast 
next
  case (4 f1 f2)
  then show ?case using cequiv_cDISJ_cong 
    by (metis bool_comb.intros(4))
qed

find_theorems finite surj
thm Finite_Set.finite_surj

lemma surj_on_finite_lemma: 
  assumes "\<And>b . b \<in> B  \<Longrightarrow> \<exists> a. a \<in> A \<and> f a = b"
     and "finite A"
   shows "finite B"
proof - 
  obtain g where "\<And>b. b \<in> B \<Longrightarrow> g b \<in> A \<and> (f (g b)) = b"
    by (metis assms(1) f_inv_into_f imageI inv_into_into)
  then have "inj_on g B"
    by (metis  inj_on_inverseI)
  show ?thesis using finite_vimage_IntI[of A g B]
    
    by (simp add: Int_absorb2 \<open>\<And>b. b \<in> B \<Longrightarrow> g b \<in> A \<and> f (g b) = b\<close> 
  \<open>inj_on g B\<close> assms(2) inf_commute subset_iff)
qed

lemma bool_comb_subseteq:
  assumes ss:"A \<subseteq> B"
  and bca:"bool_comb A f"
  shows "bool_comb B f" using bca
proof (induction f rule:bool_comb.inducts)
  case 1
  then show ?case 
    by (simp add: bool_comb.intros(1))
next
  case (2 f)
  then show ?case 
    using bool_comb.intros(2) ss by auto
next
  case (3 f)
  then show ?case 
    using bool_comb.intros(3) by blast
next
  case (4 f1 f2)
  then show ?case 
    using bool_comb.intros(4) by blast
qed

lemma finite_finite_bool_comb:
  assumes "finite ((fs:: ('m,'p) cform set) // cequiv_on TYPE('a) fs)"
  shows "finite (bool_combs fs //cequiv_on TYPE('a) (bool_combs fs))"
proof -
  obtain r where
   r:"(\<And>\<phi>s. \<phi>s \<in> fs // cequiv_on TYPE('a) fs \<Longrightarrow> r \<phi>s \<in> \<phi>s)"
   by (metis all_not_in_conv cequiv_relation_equiv 
       in_quotient_imp_non_empty)
  have aa':"\<And>a a'. a \<in> fs \<Longrightarrow> a' \<in> (cequiv_on TYPE('a) fs) `` {a} ==>
       cequiv TYPE('a) a a' "
    by (metis (no_types, lifting) Image_singleton_iff 
  case_prodD cequiv_on_def mem_Collect_eq)
  have "\<And>a a'. a \<in> fs \<Longrightarrow> (r (cequiv_on TYPE('a) fs `` {a})) \<in>  
       (cequiv_on TYPE('a) fs `` {a})" using r 
    by (meson quotientI)
  then have ceqr:"\<And>a. a \<in> fs \<Longrightarrow>  cequiv TYPE('a) a 
        (r (cequiv_on TYPE('a) fs `` {a}))" 
    by (simp add: aa')
  define R where "R = (r ` (fs // cequiv_on TYPE('a) fs))"
  have "finite R" using finite_surj assms R_def by blast
  have rR:"\<And>a. a \<in> fs \<Longrightarrow> r (cequiv_on TYPE('a) fs `` {a}) \<in> R" 
    by (simp add: R_def quotientI)
  have Rfs:"R \<subseteq> fs"
    using R_def cequiv_relation_equiv
          in_quotient_imp_subset r by fastforce
  have
  Req:"(\<And>a. a \<in> fs \<Longrightarrow> \<exists>b. b \<in> R \<and> cequiv TYPE('a) a b)"
    using ceqr rR by blast
  have "\<And>f. 
   bool_comb fs f \<Longrightarrow> \<exists>f0. bool_comb R f0 \<and> cequiv TYPE('a) f f0" 
    using bool_comb_rep_cequiv0[OF Req] by auto
  define Rq where 
    "Rq = bool_combs R //cequiv_on TYPE('a) (bool_combs R) "
  then have fRq:"finite Rq" using bool_comb_INJ_prop_cform_cequiv_choice
    using \<open>finite R\<close> by auto
   obtain c where
   c:"(\<And>\<phi>s. \<phi>s \<in> Rq \<Longrightarrow> c \<phi>s \<in> \<phi>s)" using Rq_def
    by (metis all_not_in_conv cequiv_relation_equiv 
       in_quotient_imp_non_empty)
  then have "finite (c ` Rq)" using fRq by blast
  have "(bool_combs fs //cequiv_on TYPE('a) (bool_combs fs)) \<subseteq> 
  (\<lambda> f. cequiv_on TYPE('a) (bool_combs fs) `` {f}) ` (c ` Rq)"
   
  proof (rule subsetI) 
    fix x assume 
    "x \<in> bool_combs fs // cequiv_on TYPE('a) (bool_combs fs)" 
    then obtain x0 where x0:"x0 \<in> x" and bcx0:"bool_comb fs x0"
     by (metis CollectD bool_combs_def cequiv_relation_equiv 
         ex_in_conv in_quotient_imp_non_empty 
         in_quotient_imp_subset subsetD) 
   then have "x =  cequiv_on TYPE('a) (bool_combs fs) `` {x0}"
     by (smt (verit, del_insts) Image_singleton_iff 
        \<open>x \<in> bool_combs fs // cequiv_on TYPE('a) (bool_combs fs)\<close> 
        cequiv_relation_equiv equiv_class_eq_iff quotientE)
    obtain x1 where 
    cbx1:"bool_comb R x1" and  "cequiv TYPE('a) x0 x1"
      using bool_comb_rep_cequiv0[OF Req] using bcx0 by blast
    then have bcfsx1:"bool_comb fs x1" 
      using bool_comb_subseteq cbx1 Rfs
      by blast
    then have "x1 \<in> x" 
      by (simp add: \<open>cequiv TYPE('a) x0 x1\<close> 
         \<open>x = cequiv_on TYPE('a) (bool_combs fs) `` {x0}\<close> 
         bcx0 bool_combs_def cequiv_cequiv_on)
    from bcfsx1 have xalt1:"cequiv_on TYPE('a) (bool_combs fs) `` {x1} = x"
      by (metis \<open>cequiv TYPE('a) x0 x1\<close> 
         \<open>x = cequiv_on TYPE('a) (bool_combs fs) `` {x0}\<close>
         bcx0 bool_combs_def cequiv_cequiv_on cequiv_relation_equiv
         equiv_class_eq mem_Collect_eq)
    have x1Rq:"cequiv_on TYPE('a) (bool_combs R) `` {x1} \<in> Rq"
      using Rq_def 
      by (simp add: bool_combs_def cbx1 quotientI)
    define cx1 where "cx1 = cequiv_on TYPE('a) (bool_combs R) `` {x1}"
    have Rfs:"\<And>f. bool_comb R f \<Longrightarrow> bool_comb fs f" 
      using bool_comb_subseteq cbx1 Rfs
      by blast
    have x1ccx1:"cequiv TYPE('a) x1 (c cx1)" using cx1_def c 
      by (metis (no_types, lifting) Image_singleton_iff case_prodD
         cequiv_on_def mem_Collect_eq x1Rq)
    have ccx1fs:"c cx1 \<in> (bool_combs fs)" using Rfs
      using Rq_def bool_combs_def c cequiv_relation_equiv cx1_def 
             in_quotient_imp_subset x1Rq by blast
    have "c cx1 \<in> x" using xalt1 Rfs x1ccx1 ccx1fs 
      using bcfsx1 bool_combs_def cequiv_cequiv_on by blast
    have "x = cequiv_on TYPE('a) (bool_combs fs) `` {c cx1}"
      using quotient_eqI
      by (smt (verit, ccfv_threshold) Image_singleton_iff 
     \<open>c cx1 \<in> x\<close> \<open>x = cequiv_on TYPE('a) (bool_combs fs) `` {x0}\<close> 
       cequiv_relation_equiv equiv_class_eq_iff)
    then show 
   "x \<in> (\<lambda>f. cequiv_on TYPE('a) (bool_combs fs) `` {f}) ` c ` Rq"
      using cbx1  bool_combs_def 
      using x1Rq cx1_def by blast
  qed
  then show ?thesis using finite_surj 
    using R_def \<open>finite (c ` Rq)\<close> 
    by blast
qed


lemma equiv'_cequivr:
"equiv' A (cequivr TYPE('a))"
  unfolding cequivr_def cequiv_on_def cequiv_def equiv'_def
  refl'_def sym_on_def trans_on_def
  by auto

lemma quotient'_cequivr_quotient:
"quotient' A (cequivr TYPE('a)) = A // (cequiv_on TYPE('a) A)"
  using quotient'_quotient 
  by (metis cequiv_on_cequivr equiv'_cequivr)

lemma bool_comb_INJ_prop_cform_cequiv_choice':
  assumes "finite (fs:: ('m,'p) cform set)"
  shows "finite (quotient' (bool_combs fs) (cequivr TYPE('a)) )"
  using quotient'_cequivr_quotient
  bool_comb_INJ_prop_cform_cequiv_choice
  by (metis assms)



lemma modal_operators_bool_combs:
  assumes "bool_comb s f"
  shows "modal_operators f \<subseteq> \<Union> (modal_operators ` s)" using assms
proof (induction f rule:bool_comb.induct)
  case 1
  then show ?case by simp
next
  case (2 f)
  then show ?case by blast
next
  case (3 f)
  then show ?case by simp
next
  case (4 f1 f2)
  then show ?case by simp
qed


lemma finite_finite_bool_comb':
  assumes "finite (quotient' fs (cequivr TYPE('a)))"
  shows "finite (quotient' (bool_combs fs) (cequivr TYPE('a)))"
  using finite_finite_bool_comb quotient'_cequivr_quotient
  by (metis assms)


lemma in_bool_combs:
"x \<in> bool_combs fs \<equiv> bool_comb fs x" using bool_combs_def 
  by (smt (verit) mem_Collect_eq)

end