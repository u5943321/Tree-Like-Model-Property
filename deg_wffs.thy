(* Title:        Part of the Modal Model Theory project
 * Content:      Using the idea of boolean combination to prove the finiteness
                 of formulas of degree up to k (assuming the modal language)
                 is finite. 
                 cDIAM_deg_wff_reps_properties' upgrades this to the result we 
                 need in the main proof.
 *)


theory deg_wffs
 imports Main Modal_Syntax Modal_Model Modal_Semantics 
  HOL.Equiv_Relations "HOL-Library.FuncSet" Bool_Comb 

  Disjoint_Union
begin

lemma cNOT_bool_comb_cVAR_cDIAM0:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) (cNOT phi) \<Longrightarrow>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi"
  using bool_comb.simps 
by (smt (verit, ccfv_threshold) Un_iff cform.distinct(11) 
 cform.distinct(15) cform.distinct(19) cform.distinct(5) 
 cform.inject(3) mem_Collect_eq)




lemma cNOT_bool_comb_cVAR_cDIAM:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) (cNOT phi) \<equiv>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi"
  using  cNOT_bool_comb_cVAR_cDIAM0
  by (smt (verit) Un_iff bool_comb.simps cform.distinct(11) cform.distinct(15) cform.distinct(19) 
cform.distinct(5) cform.inject(3) mem_Collect_eq)

lemma cDISJ_bool_comb_cVAR_cDIAM0:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) (cDISJ phi1 phi2) \<Longrightarrow>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi1 \<and>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi2"
  using bool_comb.cases by fastforce

lemma cDISJ_bool_comb_cVAR_cDIAM:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) (cDISJ phi1 phi2) \<equiv>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi1 \<and>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi2"
  using bool_comb.cases cDISJ_bool_comb_cVAR_cDIAM0 
  by (smt (verit, ccfv_threshold) UnE bool_comb.intros(4)
  cform.distinct(15) cform.distinct(17) cform.distinct(3) 
  cform.distinct(9) cform.inject(2) mem_Collect_eq)

lemma deg_bool_comb_prop_letters:
  "deg phi \<le> n + 1 \<and> prop_letters phi \<subseteq> s \<equiv>
  bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi"
proof (induction phi)
  case (cVAR x)
  then show ?case 
    unfolding deg.simps(2) prop_letters.simps bool_comb_cVAR
    by simp
next
  case cFALSE
  then show ?case 
    by (simp add: bool_comb.intros(1))
next
  case (cDISJ phi1 phi2)
  then show ?case  
    unfolding deg.simps(4) prop_letters.simps
    Un_subset_iff max.bounded_iff 
    cDISJ_bool_comb_cVAR_cDIAM by meson
next
  case (cNOT phi) 
  then show ?case 
    unfolding deg.simps(3) prop_letters.simps 
   cNOT_bool_comb_cVAR_cDIAM by simp
next
  case (cDIAM m fl)
  then show ?case 
    unfolding bool_comb_cDIAM cDIAM_in_Union deg.simps
  prop_letters_cDIAM_subseteq 
    by auto
qed



lemma cNOT_bool_comb_cVAR_cDIAM0_mo:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) (cNOT phi) \<Longrightarrow>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) phi"
  using bool_comb.cases 
  by blast

lemma cNOT_bool_comb_cVAR_cDIAM_mo:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) (cNOT phi) \<equiv>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and> 
      modal_operators f \<subseteq> tau}) phi"
  using  cNOT_bool_comb_cVAR_cDIAM0_mo
  by (smt (verit, del_insts) Un_iff bool_comb.cases bool_comb.intros(3) 
   cform.distinct(11) cform.inject(3) cform.simps(10) cform.simps(20)
   cform.simps(24) mem_Collect_eq)


lemma cDISJ_bool_comb_cVAR_cDIAM0_mo:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) (cDISJ phi1 phi2) \<Longrightarrow>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) phi1 \<and>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s \<and>
      modal_operators f \<subseteq> tau}) phi2"
  using bool_comb.cases by blast

lemma cDISJ_bool_comb_cVAR_cDIAM_mo:
"bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) (cDISJ phi1 phi2) \<equiv>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi1 \<and>
 bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | m fl. \<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
      prop_letters f \<subseteq> s}) phi2"
  using bool_comb.cases cDISJ_bool_comb_cVAR_cDIAM0_mo
  by (smt (verit, ccfv_threshold) UnE bool_comb.intros(4)
  cform.distinct(15) cform.distinct(17) cform.distinct(3) 
  cform.distinct(9) cform.inject(2) mem_Collect_eq)

lemma deg_bool_comb_prop_letters_modal_operators:
  "deg phi \<le> n + 1 \<and> prop_letters phi \<subseteq> s \<and> 
   modal_operators phi \<subseteq> tau
   \<equiv>
  bool_comb ({cVAR v | v. v \<in> s} \<union>
     {cDIAM m fl | 
      m fl. m \<in> tau \<and>
      (\<forall>f. f \<in> set fl \<longrightarrow> deg f \<le> n \<and> 
          prop_letters f \<subseteq> s \<and>
          modal_operators f \<subseteq> tau)}) phi"
proof (induction phi)
  case (cVAR x)
  then show ?case 
    unfolding deg.simps(2) prop_letters.simps bool_comb_cVAR
    by simp
next
  case cFALSE
  then show ?case 
    by (simp add: bool_comb.intros(1))
next
  case (cDISJ phi1 phi2)
  then show ?case  
    unfolding deg.simps(4) prop_letters.simps
    Un_subset_iff max.bounded_iff 
    cDISJ_bool_comb_cVAR_cDIAM_mo 
    by (smt (verit, del_insts) UnE bool_comb.cases bool_comb.intros(4) 
cform.distinct(3) cform.distinct(9) cform.inject(2) cform.simps(20) 
cform.simps(22) le_sup_iff mem_Collect_eq modal_operators.simps(3)) 
  
next
  case (cNOT phi) 
  then show ?case 
    unfolding deg.simps(3) prop_letters.simps 
   cNOT_bool_comb_cVAR_cDIAM_mo 
    by (smt (verit, best) UnE bool_comb.cases bool_comb.intros(3)
 cform.distinct(11) cform.inject(3) cform.simps(10) cform.simps(20) 
cform.simps(24) mem_Collect_eq modal_operators.simps(4))
  next
  case (cDIAM m fl)
  then show ?case 
    unfolding bool_comb_cDIAM cDIAM_in_Union deg.simps
    using
  prop_letters_cDIAM_subseteq modal_operators_cDIAM_subseteq 
    by auto
qed

lemma cDISJ_bool_comb:
  assumes bcf: "bool_comb s f"
  and "f \<notin> s"
  and "f = cDISJ phi1 phi2"
 shows "bool_comb s phi1 \<and> bool_comb s phi2"
  using assms
proof (induction f rule:bool_comb.induct)
  case 1
  then show ?case  by simp
next
  case (2 f)
  then show ?case  by blast
next
  case (3 f)
  then show ?case by blast
next
  case (4 f1 f2)
  then show ?case by blast
qed


lemma cNOT_bool_comb:
  assumes bcf: "bool_comb s f"
  and "f \<notin> s"
  and "f = cNOT phi"
 shows "bool_comb s phi"
  using assms
proof (induction f rule:bool_comb.induct)
  case 1
  then show ?case  by simp
next
  case (2 f)
  then show ?case  by blast
next
  case (3 f)
  then show ?case by blast
next
  case (4 f1 f2)
  then show ?case by blast
qed

definition comb_set :: "('m,'p) sig \<Rightarrow> nat \<Rightarrow> ('m,'p) cform set"
  where 
"comb_set sig n = 
 {cVAR v |v. v \<in> props sig} \<union>
 {\<diamondsuit>m fl |m fl. 
   m \<in> ops sig \<and> 
   length fl = arity sig m \<and> 
   (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> deg_wffs n sig)}"


lemma cDISJ_bool_comb_set_lemma:
"bool_comb (comb_set sig n) (cDISJ phi1 phi2) \<Longrightarrow>
 bool_comb (comb_set sig n) phi1 \<and>
 bool_comb (comb_set sig n) phi2"
  unfolding comb_set_def
  using cDISJ_bool_comb by blast

lemma cDISJ_bool_comb_set:
"bool_comb (comb_set sig n) (cDISJ phi1 phi2) \<longleftrightarrow>
 bool_comb (comb_set sig n) phi1 \<and>
 bool_comb (comb_set sig n) phi2"
  using cDISJ_bool_comb_set_lemma 
  using bool_comb.intros(4) by blast


lemma cNOT_bool_comb_set_lemma:
"bool_comb (comb_set sig n) (cNOT phi) \<Longrightarrow>
 bool_comb (comb_set sig n) phi"
  unfolding comb_set_def
  using cNOT_bool_comb by blast

lemma cNOT_bool_comb_set:
"bool_comb (comb_set sig n) (cNOT phi) \<longleftrightarrow>
 bool_comb (comb_set sig n) phi"
  using cNOT_bool_comb_set_lemma 
  using bool_comb.intros(3) by blast



lemma deg_wff_lemma:
  "phi \<in> deg_wffs (n+ 1) sig
   \<equiv>
  bool_comb (comb_set sig n) phi"
  unfolding  deg_wffs_def mem_Collect_eq comb_set_def
proof (induction phi)
  case (cVAR x)
  then show ?case 
    unfolding deg.simps(2) prop_letters.simps bool_comb_cVAR
    by (simp add: wff_cVAR)
next
  case cFALSE
  then show ?case 
    by (simp add: bool_comb.intros(1) wff_cFALSE)
next
  case (cDISJ phi1 phi2)
  then show ?case  
    unfolding deg.simps(4) prop_letters.simps
    Un_subset_iff max.bounded_iff 
    cDISJ_bool_comb_set wff_cDISJ 
    by (smt (verit, del_insts) Un_iff bool_comb.intros(4)
  cDISJ_bool_comb cform.distinct(3) cform.simps(22) mem_Collect_eq)
next
  case (cNOT phi) 
  then show ?case 
    unfolding deg.simps(3)
    by (smt (verit, ccfv_threshold) UnE bool_comb.intros(3) cNOT_bool_comb cform.distinct(19) 
   cform.simps(10) mem_Collect_eq wff_cNOT)
  next
  case (cDIAM m fl)
  then show ?case 
    unfolding bool_comb_cDIAM cDIAM_in_Union deg.simps
    wff_cDIAM by auto
qed



lemma deg_wffs_bool_combs:
"deg_wffs (n+ 1) sig = 
 bool_combs (comb_set sig n)"
  using  deg_wff_lemma unfolding deg_wffs_def bool_combs_def
  by blast

lemma deg_wffs_0:
  "deg_wffs 0 sig = bool_combs (cVAR ` (props sig))"
  unfolding bool_combs_def deg_wffs_def set_eq_iff mem_Collect_eq
  Pure.symmetric [OF bool_comb_prop_cform] Nat.bot_nat_0.extremum_unique
  deg_0_propform 
  using wff_prop_cform
  by blast

definition cDIAMs_set:: "nat \<Rightarrow> ('m,'p) sig \<Rightarrow> ('m,'p) cform set"
  where 
"cDIAMs_set n sig = 
 {\<diamondsuit>m fl |m fl. m \<in> ops sig \<and> length fl = arity sig m \<and>
  (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> deg_wffs n sig)}"

lemma quotient'_comb_set:
"quotient' (comb_set sig n) (cequivr TYPE('a)) = 
 quotient' (cVAR ` (props sig)) (cequivr TYPE('a)) \<union>
 quotient' (cDIAMs_set n sig) (cequivr TYPE('a))"
proof -
  have 
  "(comb_set sig n) = 
  (cVAR ` (props sig)) \<union> (cDIAMs_set n sig)" 
    unfolding comb_set_def cDIAMs_set_def 
    by blast
  have 
  "quotient' ((cVAR ` (props sig)) \<union> (cDIAMs_set n sig)) (cequivr TYPE('a)) = 
  quotient' (cVAR ` (props sig)) (cequivr TYPE('a)) \<union>
  quotient' (cDIAMs_set n sig) (cequivr TYPE('a))"
  proof (rule equiv_on_disjoint_partition)
    show 
    "equiv' (cVAR ` props sig \<union> cDIAMs_set n sig) (cequivr TYPE('a))"
      using equiv'_cequivr by blast
    show "\<And>a b. a \<in> cVAR ` props sig \<Longrightarrow> 
          b \<in> cDIAMs_set n sig \<Longrightarrow> (a, b) \<notin> cequivr TYPE('a)"
      using NOT_cequiv_cVAR_cDIAM 
      by (smt (verit, best) CollectD cDIAMs_set_def 
        case_prodD cequiv_on_def cequivr_def image_iff)
  qed
  then show ?thesis
    using \<open>comb_set sig n = cVAR ` props sig \<union> cDIAMs_set n sig\<close> by presburger
qed

lemma finite_finite_quotient_cVAR:
  assumes "finite (props sig)"
  shows "finite (quotient' (cVAR ` (props sig)) (cequivr TYPE('a)))"
 using finite_finite_quotient' assms by auto


definition cDIAM_set:: "'m \<Rightarrow> nat \<Rightarrow> ('m,'p) sig \<Rightarrow> ('m,'p) cform set"
  where 
"cDIAM_set m n sig = 
 {\<diamondsuit>m fl |fl. length fl = arity sig m \<and>
  (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> deg_wffs n sig)}"

lemma cDIAMs_set_cDIAM_set:
"cDIAMs_set n sig = ( \<Union>m\<in> (ops sig). (cDIAM_set m n sig))"
  unfolding cDIAMs_set_def cDIAM_set_def set_eq_iff 
  mem_Collect_eq  UN_iff Bex_def by metis
  

lemma quotient'_split:
"quotient' (\<Union>x \<in> A. P x) r = 
 (\<Union>x \<in> A. (rclass (\<Union>x \<in> A. P x) r ` (P x)))"
  unfolding quotient'_def set_eq_iff mem_Collect_eq UN_iff Bex_def 
  by auto

lemma quotient'_split':
"quotient' (\<Union>x \<in> A. P x) r = 
 ((rclass (\<Union>x \<in> A. P x) r ` (\<Union>x \<in> A.  (P x))))"
  unfolding quotient'_def set_eq_iff mem_Collect_eq UN_iff Bex_def 
  by auto

lemma quotient'_cDIAMs_set_split_lemma:
 "(quotient' (cDIAMs_set n sig) (cequivr TYPE('a))) = 
  (rclass (cDIAMs_set n sig)
    (cequivr TYPE('a)) ` (\<Union>x\<in>ops sig. cDIAM_set x n sig))"
  unfolding cDIAMs_set_cDIAM_set quotient'_split' by auto

lemma rclass_eq:
  assumes "equiv' s r"
  and "x1 \<in> s"
  and "x2 \<in> s"
  and "(x1,x2)\<in> r"
shows "rclass s r x1 = rclass s r x2" using assms
  unfolding rclass_def set_eq_iff mem_Collect_eq 
  equiv'_def sym_on_def trans_on_def 
  by blast

lemma on_quotient'_surj_lemma:
  assumes 
  "\<And>phi. phi \<in> s \<Longrightarrow> (\<exists>phi0. phi0 \<in> A \<and> (phi0,phi) \<in> r)"
 and "equiv' s r"
 and "A \<subseteq> s"
shows 
  "quotient' s r \<subseteq> rclass s r ` A"
  unfolding quotient'_def 
proof (intro subsetI,unfold mem_Collect_eq ex_neg_all_pos)  
  show "\<And>x a. x = rclass s r a \<and> a \<in> s \<Longrightarrow> x \<in> rclass s r ` A"
    using equiv'_subset rclass_eq
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) image_eqI subsetD)
qed

definition cDIAMs_comb::"('m,'p) sig \<Rightarrow> ('m,'p) cform set \<Rightarrow>  ('m,'p) cform set "
  where
"cDIAMs_comb sig s = 
{cDIAM m fl |m fl. m \<in> ops sig \<and> length fl = arity sig m \<and> 
 (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> s)}"

lemma collect_a_subset_of_cDIAMs_set:
  assumes 
  "\<And>r. r \<in> s \<Longrightarrow> r \<in> deg_wffs n sig"
shows 
  "cDIAMs_comb sig s \<subseteq> (cDIAMs_set n sig)"
  unfolding cDIAMs_comb_def cDIAMs_set_def
  using assms by auto

definition cDIAMs_m_comb::"'m \<Rightarrow> ('m,'p) sig \<Rightarrow> ('m,'p) cform set \<Rightarrow>
  ('m,'p) cform set "
  where
"cDIAMs_m_comb m sig s = 
{cDIAM m fl |fl. length fl = arity sig m \<and> 
 (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> s)}"

definition m_fl_set:: "'m \<Rightarrow> ('m,'p)sig => ('m,'p) cform set =>
('m \<times> ( ('m,'p) cform list) ) set" where
"m_fl_set m sig s = 
 {(m,fl) | fl. length fl = arity sig m \<and>  set fl\<subseteq> s}"


lemma cDIAMs_comb_cDIAMs_m_comb:
"cDIAMs_comb sig s = (\<Union> m\<in> (ops sig). cDIAMs_m_comb m sig s) "
  unfolding cDIAMs_comb_def cDIAMs_m_comb_def 
  by blast

lemma m_fl_set_Image:
 "m_fl_set m sig s = 
 (\<lambda>fl. (m,fl)) ` {fl. set fl \<subseteq> s \<and> length fl = arity sig m}"
  unfolding m_fl_set_def 
  by blast


lemma m_fl_set_finite:
  assumes "finite s"
  shows "finite (m_fl_set m sig s )"
  unfolding m_fl_set_Image using finite_lists_length_eq
 m_fl_set_Image 
  using assms by blast


lemma cDIAMs_m_comb_finite:
  assumes "finite s"
shows "finite (cDIAMs_m_comb m sig s)" 
proof - 
  have "(cDIAMs_m_comb m sig s) = 
   (\<lambda>(m,fl). cDIAM m fl) ` (m_fl_set m sig s )"
    unfolding cDIAMs_m_comb_def m_fl_set_def
    by fastforce
  then show ?thesis using finite_surj 
    by (simp add: assms m_fl_set_finite)
qed

lemma finite_cDIAMs_comb_finite:
  assumes "finite (ops sig)"
  and "finite s"
shows "finite (cDIAMs_comb sig s)" 
proof -
  have "cDIAMs_comb sig s = (\<Union> m\<in> (ops sig). cDIAMs_m_comb m sig s)"
    using cDIAMs_comb_cDIAMs_m_comb.
  show ?thesis using finite_UN cDIAMs_m_comb_finite assms
    by (metis \<open>cDIAMs_comb sig s = (\<Union>m\<in>ops sig. cDIAMs_m_comb m sig s)\<close>)
qed

lemma collected_subset_deg_wffs:
  assumes "\<And>c. c \<in> (quotient' (deg_wffs n sig) (cequivr TYPE('a))) \<Longrightarrow>
 f c \<in> c"
  shows "f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a))) 
  \<subseteq> (deg_wffs n sig)" using assms
  unfolding quotient'_def mem_Collect_eq ex_neg_all_pos rclass_def
  by blast


lemma collected_subset_finite:
  assumes "finite (quotient' (deg_wffs n sig) (cequivr TYPE('a)))"
  and "finite (ops sig)"
shows "finite (cDIAMs_comb sig (f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a))) )) "
  using finite_cDIAMs_comb_finite finite_surj 
  using assms(1) assms(2) by blast 



lemma in_cDIAMs_set:
 "phi \<in> cDIAMs_set n sig \<equiv> 
 
  \<exists>m fl. phi = cDIAM m fl \<and> m \<in> ops sig \<and> length fl = arity sig m \<and>
  (\<forall>f. f \<in> set fl \<longrightarrow> f \<in> deg_wffs n sig)"
  unfolding  cDIAMs_set_def mem_Collect_eq by simp

lemma cDIAM_set_cDIAM_comb_EXISTS:
  assumes phi:"phi \<in> cDIAMs_set n sig"
  and f:"\<And>c. c \<in> (quotient' (deg_wffs n sig) (cequivr TYPE('a))) \<Longrightarrow>
 f c \<in> c"
shows "\<exists>phi0. phi0 \<in> cDIAMs_comb sig 
  (f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a)))) \<and> 
  cequiv TYPE('a) phi0 phi"
  using assms 
proof -
  obtain m fl where 
     phi_m_fl:"phi = cDIAM m fl"
  and m_in_ops:"m \<in> ops sig" 
  and m_arity:"length fl = arity sig m"
  and fl_deg_wff: "\<And>f. f \<in> set fl \<Longrightarrow> f \<in> deg_wffs n sig" 
    using phi unfolding in_cDIAMs_set ex_neg_all_pos by blast
  define phi0 where
  "phi0 = cDIAM m 
  (map (f o (rclass (deg_wffs n sig) (cequivr TYPE('a)))) fl)"
  have in_fl_f:"\<And>fm. fm \<in> set fl \<Longrightarrow> 
        f (rclass (deg_wffs n sig) (cequivr TYPE('a)) fm) \<in>
       (rclass (deg_wffs n sig) (cequivr TYPE('a)) fm)
          " using f quotient'_def 
    using fl_deg_wff by blast
  
  {
    fix fm
    assume fm_in_fl:"fm \<in> set fl"
    have x: " cequiv TYPE('a)
  (f (rclass (deg_wffs n sig) (cequivr TYPE('a)) fm)) fm"
      using  in_rclass_equiv'[OF equiv'_cequivr fl_deg_wff[OF fm_in_fl]] 
       in_fl_f[OF fm_in_fl]
      using cequiv_on_def cequivr_def by fastforce
  }
  note cequivs_fl = this
  have f_cfm_fm: "\<And>fm. fm \<in> set fl \<Longrightarrow>
       cequiv TYPE('a)
  (f (rclass (deg_wffs n sig) (cequivr TYPE('a)) fm)) fm
          " 
    using in_rclass_equiv'[OF equiv'_cequivr]  cequivs_fl by auto

  have phi0_in_comb:"phi0 \<in> cDIAMs_comb sig 
  (f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a))))" 
    unfolding cDIAMs_comb_def mem_Collect_eq
    using fl_deg_wff m_in_ops m_arity 
    using phi0_def quotient'_def by fastforce
  have "\<And>r fm. (r,fm) \<in> 
  set (zip (map (f o (rclass (deg_wffs n sig) (cequivr TYPE('a)))) fl) fl)
  \<Longrightarrow> cequiv TYPE('a) r fm"
    using f_cfm_fm 
    by (smt (verit, del_insts) in_set_zip nth_map o_apply 
       prod.sel(1) prod.sel(2) set_zip_rightD)

  then have "phi0 \<in> cDIAMs_comb sig 
  (f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a)))) \<and> 
  cequiv TYPE('a)  phi0 phi"
    using cDIAM_cequiv_cong phi_m_fl
    using phi0_def phi0_in_comb by fastforce
   
  then show ?thesis by blast
qed


lemma quotient'_cequivr_rep_EXISTS:
"\<exists>f. \<forall>c. c \<in> quotient' A (cequivr TYPE('a)) \<longrightarrow> f c \<in> c"
  using quotient'_selection_EXISTS equiv'_cequivr by blast

lemma finite_quotient'_finite_cDIAMs_set:
  assumes finq:"finite (quotient' (deg_wffs n sig) (cequivr TYPE('a)))"
   assumes fintau:"finite (ops sig)"
   shows "finite (quotient' (cDIAMs_set n sig) (cequivr TYPE('a)))"
  
proof - 
  obtain f where 
  f:"\<And>c. c \<in> (quotient' (deg_wffs n sig) (cequivr TYPE('a))) \<Longrightarrow>
 f c \<in> c" using quotient'_cequivr_rep_EXISTS by metis
  have 
  fin:"finite 
  (rclass (cDIAMs_set n sig) (cequivr TYPE('a)) `
        cDIAMs_comb sig (f ` quotient' (deg_wffs n sig) (cequivr TYPE('a))))"
    using  finite_cDIAMs_comb_finite finq finite_surj fintau by blast
  have
  ss:"quotient' (cDIAMs_set n sig) (cequivr TYPE('a))
     \<subseteq> rclass (cDIAMs_set n sig) (cequivr TYPE('a)) `
        cDIAMs_comb sig (f ` quotient' (deg_wffs n sig) (cequivr TYPE('a)))"
  proof (intro
 on_quotient'_surj_lemma[of "cDIAMs_set n sig" 
 "cDIAMs_comb sig 
  (f ` (quotient' (deg_wffs n sig) (cequivr TYPE('a))))"
 "cequivr TYPE('a)"])
    show " equiv' (cDIAMs_set n sig) (cequivr TYPE('a))"
      using equiv'_cequivr by blast
    show 
  "cDIAMs_comb sig 
   (f ` quotient' (deg_wffs n sig) (cequivr TYPE('a))) \<subseteq>
   cDIAMs_set n sig"
      using collect_a_subset_of_cDIAMs_set
       collected_subset_deg_wffs f subsetD by blast
    show 
    "\<And>phi. phi \<in> cDIAMs_set n sig \<Longrightarrow>
       \<exists>phi0.
       phi0 \<in> cDIAMs_comb sig 
         (f ` quotient' (deg_wffs n sig) (cequivr TYPE('a))) \<and>
              (phi0, phi) \<in> cequivr TYPE('a)"
      using cDIAM_set_cDIAM_comb_EXISTS f 
     
      by (metis UNIV_I cequiv_cequiv_on cequivr_def)
  qed
  show ?thesis using finite_subset
    using fin ss by blast
qed

lemma prop_2_29:
  assumes fins:"finite (props sig)"
  assumes fintau:"finite (ops sig)"
  shows "finite 
  (quotient' (deg_wffs n sig)
  (cequivr TYPE('a)))"
proof (induction n)
  case 0
  then show ?case using deg_wffs_0
    by (metis assms(1) bool_comb_INJ_prop_cform_cequiv_choice' finite_imageI)
next
  case (Suc n)
  then show ?case unfolding Suc_eq_plus1 deg_wffs_bool_combs
  proof (intro finite_finite_bool_comb',
         unfold  quotient'_comb_set)
    show " finite (quotient' (cVAR ` props sig) (cequivr TYPE('a)) \<union> 
   quotient' (cDIAMs_set n sig) (cequivr TYPE('a)))" 
      using finite_finite_quotient_cVAR
   finite_quotient'_finite_cDIAMs_set
      using Suc fins fintau by blast
  qed
qed

definition pick_diams where
"pick_diams TYPE('a) n sig s  \<equiv> 
 \<forall>m fl. cDIAM m fl \<in> deg_wffs n sig \<longrightarrow>
 (\<exists>fl1. cDIAM m fl1 \<in> s \<and> cequiv (TYPE ('a)) (cDIAM m fl) (cDIAM m fl1))
 "


lemma cTRUE_deg_wff:
"cNOT cFALSE \<in> deg_wffs n sig"
  unfolding deg_wffs_def mem_Collect_eq deg.simps
  by (simp add: cFALSE wff_cNOT)

lemma cCONJ_deg_wffs:
"cCONJ f1 f2 \<in> deg_wffs n sig \<equiv> 
 f1 \<in> deg_wffs n sig \<and> f2 \<in> deg_wffs n sig"
  unfolding deg_wffs_def mem_Collect_eq cCONJ_def
  by (smt (verit) deg.simps(3) deg.simps(4) max.bounded_iff wff_cDISJ wff_cNOT)


lemma deg_wffs_finite_bigconj:
  assumes finfs:"finite fs"
  and "fs \<subseteq> deg_wffs n sig"
  and "fs \<noteq> {}"
shows "\<exists>ff. ff \<in> deg_wffs n sig \<and> 
  (\<forall>M w::'a. (asatis M w ff \<longleftrightarrow> 
         (\<forall>f. f \<in> fs \<longrightarrow> asatis M w f)))"
  using assms
proof (induction)
  case empty
  then show ?case by simp
 
next
  case (insert x F)
  then show ?case
  proof - 
    from insert 
    have F:"F \<subseteq> deg_wffs n sig" 
    and x: "x \<in>  deg_wffs n sig"by auto
    consider (c1) "F = {}" | (c2) "F \<noteq> {}" by blast
    then show ?case
    proof cases
      case c1
      then have 
      "x \<in> deg_wffs n sig \<and>
         (\<forall>M w. asatis M w x =
                (\<forall>f. f \<in> insert x F \<longrightarrow>
                     asatis M w f))" 
        using insert x by simp
      then show ?thesis by metis
    next
      case c2
      then obtain ff where "ff \<in> deg_wffs n sig \<and>
         (\<forall>M w::'a. asatis M w ff =
                (\<forall>f. f \<in> F \<longrightarrow> asatis M w f))"
        using insert c2 F by blast
      then have 
      "cCONJ x ff \<in> deg_wffs n sig \<and>
         (\<forall>M w::'a. asatis M w (cCONJ x ff) =
                (\<forall>f. f \<in> insert x F \<longrightarrow>
                     asatis M w f))" 
        unfolding  cCONJ_deg_wffs asatis_cCONJ
        using x by blast
      then show ?thesis by blast
    qed
qed
qed


lemma deg_wffs_finite_cequiv_EXISTS:
  assumes fins:"finite (props sig)"
  and fintau:"finite (ops sig)" 
shows "\<exists>s. finite s \<and> s \<subseteq> deg_wffs n sig \<and>
        ( \<forall>phi. phi \<in> deg_wffs n sig \<longrightarrow>
              (\<exists> rf. rf \<in> s \<and> cequiv TYPE('a) phi rf))"
proof -
  define Q where "Q \<equiv> (quotient' (deg_wffs n sig)
  (cequivr TYPE('a)))" 
  obtain f where 
  f:"\<And>c. c \<in> Q \<Longrightarrow> f c \<in> c"
    using quotient'_cequivr_rep_EXISTS Q_def by metis
  then have "finite (f ` Q)"
    using prop_2_29 Q_def fins fintau by blast
  {fix phi assume "phi \<in> f ` Q" 
    then have "phi \<in> deg_wffs n sig" 
      unfolding Q_def quotient'_def f 
      using Q_def \<open>phi \<in> f ` Q\<close> collected_subset_deg_wffs f by blast
  }
  {fix phi assume phi: "phi \<in> deg_wffs n sig"
  define rp where "rp \<equiv> rclass (deg_wffs n sig) (cequivr TYPE('a)) phi"
  have "rp \<in> Q" unfolding rp_def Q_def quotient_def
    using phi quotient'_def by auto
  then have frp:"f rp \<in> rp" using f by metis
  then have "cequiv TYPE('a) phi (f rp)" 
    by (metis (no_types, lifting) case_prodD cequiv_def 
cequiv_on_def cequivr_def equiv'_cequivr in_rclass_equiv' 
 mem_Collect_eq phi rp_def)
  then have "(\<exists> rf. rf \<in> f ` Q \<and> cequiv TYPE('a) phi rf)" 
    using frp \<open>rp \<in> Q\<close> by blast
}
  then show ?thesis 
    by (metis Q_def \<open>finite (f ` Q)\<close> collected_subset_deg_wffs f)
qed


lemma prop_2_29_coro:
  assumes fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
  and "fs \<subseteq> deg_wffs n sig"
  and "fs \<noteq> {}"
shows "\<exists>ff. ff \<in> deg_wffs n sig \<and>  
  (\<forall>M w::'a. asatis M w ff \<longleftrightarrow> 
    (\<forall>f. f \<in> fs \<longrightarrow> asatis M w f))"
proof - 
  from fins fintau obtain s where 
   fins: "finite s"
   and "s \<subseteq> deg_wffs n sig"
   and "\<And>phi. phi \<in> deg_wffs n sig \<Longrightarrow>
              (\<exists> rf. rf \<in> s \<and> cequiv TYPE('a) phi rf)"
    using deg_wffs_finite_cequiv_EXISTS by metis
  then have
   "\<And>phi. phi \<in> fs \<Longrightarrow> (\<exists>rf. rf \<in> s \<and> cequiv TYPE('a) phi rf)"
    using  assms(3) by auto
  then obtain f where
  f:"\<And>phi. phi \<in> fs \<Longrightarrow> f phi \<in> s \<and> cequiv TYPE('a) phi (f phi)"
    by metis
  then have finim: "finite (f ` fs)" 
    by (meson finite_subset fins image_subsetI)
  have ss: "(f ` fs) \<subseteq> deg_wffs n sig" 
    using \<open>s \<subseteq> deg_wffs n sig\<close> f by blast
  have imnot0:"f ` fs \<noteq> {}"  by (simp add: assms(4))
  then obtain ff where
  "ff \<in> deg_wffs n sig \<and> 
  (\<forall>M w::'a. (asatis M w ff \<longleftrightarrow> 
         (\<forall>phi. phi \<in> (f ` fs) \<longrightarrow> asatis M w phi)))"
    using  deg_wffs_finite_bigconj[OF finim ss imnot0] 
    by auto
  have feqv:"\<And>phi. phi \<in> fs \<Longrightarrow> cequiv TYPE('a) phi (f phi)"
    using f by auto
  {fix M fix w :: 'a fix phi
    assume "asatis M w ff" and "phi \<in> fs"
    then have "f phi \<in> f ` fs"  by blast 
    then have "cequiv TYPE('a) phi (f phi)" using f 
      using \<open>phi \<in> fs\<close> by blast
    then have "asatis M w phi" using cequiv_def 
      by (metis \<open>asatis M w ff\<close> \<open>f phi \<in> f ` fs\<close> 
       \<open>ff \<in> deg_wffs n sig \<and> 
      (\<forall>M w. asatis M w ff = (\<forall>phi. phi \<in> f ` fs \<longrightarrow> asatis M w phi))\<close>)
  }
  {fix M fix w :: 'a fix phi 
    assume fssat:"(\<forall>f. f \<in> fs \<longrightarrow> asatis M w f)"
    assume "phi \<in> f ` fs"
    then obtain f0 where "f0 \<in> fs" and "phi = f f0" by blast
    then have "cequiv TYPE('a) f0 phi" using f by blast
    then have "asatis M w phi" using fssat
      by (meson \<open>f0 \<in> fs\<close> cequiv_def)
  }
  then show ?thesis
    by (metis \<open>\<And>w phi M. \<lbrakk>asatis M w ff; phi \<in> fs\<rbrakk> \<Longrightarrow> asatis M w phi\<close> \<open>ff \<in> deg_wffs n sig \<and> 
(\<forall>M w. asatis M w ff = (\<forall>phi. phi \<in> f ` fs \<longrightarrow> asatis M w phi))\<close>)
qed


thm deg_wffs_def
lemma bigconj_deg_wffs_worlds0:
  assumes w0:"w0 \<in> world M0"
  and fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
shows "\<exists>\<Phi>. \<Phi> \<in> deg_wffs n sig \<and>
           (\<forall>M w. asatis M w \<Phi> \<longleftrightarrow> 
            (\<forall>f. f \<in> deg_wffs n sig \<and> asatis M0 w0 f \<longrightarrow>
                asatis M w f))"
proof - 
  define fs where "fs \<equiv> {f.  f \<in> deg_wffs n sig \<and> asatis M0 w0 f }"
  have fsnon0:"fs \<noteq> {}" using w0 asatis_cTRUE 
    by (metis CollectI cTRUE_def cTRUE_deg_wff emptyE fs_def)
  have fsss:"fs \<subseteq> deg_wffs n sig" using fs_def by blast
  with fsnon0 show ?thesis 
    using prop_2_29_coro[OF fins fintau fsss fsnon0]
    using fs_def by auto
qed


lemma bigconj_deg_wffs_worlds:
  assumes ss:"w0s \<subseteq> world M0"
  and fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
shows "\<exists>\<Phi>. 
          \<forall>w0. w0 \<in> w0s \<longrightarrow>
          \<Phi> w0 \<in> deg_wffs n sig \<and>
         (\<forall>M w. asatis M w (\<Phi> w0) \<longleftrightarrow> 
            (\<forall>f. f \<in> deg_wffs n sig \<and> asatis M0 w0 f \<longrightarrow>
                asatis M w f))"
proof - 
  from assms have 
  "\<And>w0. w0 \<in> w0s \<Longrightarrow>
    \<exists>phi. phi \<in> deg_wffs n sig \<and>
     (\<forall>M w. asatis M w phi \<longleftrightarrow> 
            (\<forall>f. f \<in> deg_wffs n sig \<and> asatis M0 w0 f \<longrightarrow>
                asatis M w f))"
    using bigconj_deg_wffs_worlds0[OF _ fins fintau]
    by (smt (verit, ccfv_threshold) subset_eq)
  then show ?thesis
    by (metis (mono_tags, opaque_lifting))
qed


definition deg_thy :: "('a::type) itself \<Rightarrow>nat
     \<Rightarrow> ('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set
        \<Rightarrow> 'a set \<times>
           ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<times>
           ('p \<Rightarrow> 'a \<Rightarrow> bool)
           \<Rightarrow> 'a \<Rightarrow> ('m, 'p) cform \<Rightarrow> bool" where
 "deg_thy (TYPE('a)) n sig M w \<phi> \<equiv>
  \<phi> \<in> deg_wffs n sig \<and>
  (\<forall>M1 w1::'a.
   asatis M1 w1 \<phi> \<longleftrightarrow>
   (\<forall>f. f \<in> deg_wffs n sig \<and> asatis M w f \<longrightarrow>
                asatis M1 w1 f))"

lemma deg_thy_satis_self:
  assumes "deg_thy (TYPE('a)) n sig M w \<phi>"
  shows "asatis M (w::'a) \<phi>"
  using deg_thy_def
  by (metis assms)

lemma deg_thy_EXISTS:
  assumes w:"w \<in> world M"
  and fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
shows "\<exists>\<phi>. deg_thy (TYPE('a)) n sig M w \<phi>"
  unfolding  deg_thy_def
  using  bigconj_deg_wffs_worlds0[OF w fins fintau]
  by blast

  
lemma deg_thy_choice:
  assumes ss:"ws \<subseteq> world M"
  and fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
shows "\<exists>\<Phi>. 
          \<forall>w. w \<in> ws \<longrightarrow> deg_thy (TYPE('a)) n sig M w (\<Phi> w)"
  using deg_thy_EXISTS 
  by (metis fins fintau ss subset_iff)

lemma bigconj_deg_wffs_mk_cDIAM:
  assumes ss:"set ul \<subseteq> world M"
  and fins:"finite (props sig)"
  and fintau:"finite (ops sig)"
shows "\<exists>phil. 
       length phil = length ul \<and> 
       (\<forall>u phi. (u,phi) \<in> set (zip ul phil) \<longrightarrow>
        deg_thy (TYPE('a)) n sig M u phi )"
proof - 
  from ss fins deg_thy_choice obtain \<Phi> where
   a:"\<And>w. w \<in> set ul \<Longrightarrow> 
        deg_thy (TYPE('a)) n sig M w (\<Phi> w)"
    using fintau by blast
 
  {fix u phi
    assume "(u,phi) \<in> set (zip ul (list.map \<Phi> ul))"
    then have 
    "deg_thy (TYPE('a)) n sig M u phi"
      using a 
      by (metis fst_conv in_set_zip nth_map set_zip_leftD snd_conv)
  }
  then show ?thesis 
    using length_map by blast
  
qed


lemma deg_wffs_cDIAM_step:
  assumes fl:"\<And>f. f \<in> set fl \<Longrightarrow> f \<in> deg_wffs n sig"
   and "m \<in> ops sig"
   and "length fl = arity sig m"
 shows "cDIAM m fl \<in> deg_wffs (n+1) sig" using assms
  unfolding deg_wffs_def mem_Collect_eq using wff.simps
  by (metis deg_cDIAM_Suc)

abbreviation Choice where "Choice \<equiv> Eps o Nunchaku.rmember"


lemma Choice_in_set:
  assumes " s \<noteq> {}"
  shows "Choice s \<in> s" 
  by (metis Collect_empty_eq Collect_mem_eq assms comp_apply rmember_def someI)


definition cDIAM_deg_wff_reps where
"cDIAM_deg_wff_reps TYPE('a) n sig \<equiv>
Choice `
 ((\<lambda>c. c \<inter> {f. \<exists>m fl. f = cDIAM m fl}) ` (quotient' (deg_wffs n sig) (cequivr TYPE('a))) - {{}} )
"


lemma in_rclass_cequiv:
  assumes "f \<in> rclass (deg_wffs n sig) (cequivr TYPE('a)) f0"
  shows "cequiv TYPE('a) f f0"
  by (metis (no_types, lifting) assms case_prodD 
 cequiv_on_def cequivr_def equiv'_cequivr 
 in_rclass_equiv' mem_Collect_eq rclass_def)

lemma finite_cDIAM_deg_wff_reps:
  assumes a1:"finite (props sig)"
  and a2:"finite (ops sig)"
shows "finite (cDIAM_deg_wff_reps TYPE('a) n sig)"
  using prop_2_29[OF a1 a2, of n ] cDIAM_deg_wff_reps_def 
  by (smt (verit) finite_Diff finite_imageI)

  

lemma cDIAM_deg_wff_reps_properties:
  assumes "cDIAM m fl \<in> deg_wffs n sig"
    and infinite:"infinite (UNIV::'a set)"
    and "\<not>cequiv TYPE('a) (cDIAM m fl) cFALSE"
  shows "\<exists>fl'. cDIAM m fl' \<in> cDIAM_deg_wff_reps TYPE('a) n sig \<and>
    cequiv TYPE('a) (cDIAM m fl) (cDIAM m fl') \<and>
    length fl = length fl' \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (fl' ! j))"
proof - 
  from assms 
  have "rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<in> 
       (quotient' (deg_wffs n sig) (cequivr TYPE('a)))"
    by (simp add: equiv'_cequivr quotient'_quotient quotientI rclass_Image)
  have "cDIAM m fl  \<in> rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<inter> 
  {f. \<exists>m fl. f = cDIAM m fl}"
    by (simp add: assms equiv'_cequivr rclass_non_empty)
  then have
  c: "Choice 
  (rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<inter> {f. \<exists>m fl. f = cDIAM m fl})
  \<in>
   rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<inter> {f. \<exists>m fl. f = cDIAM m fl}
" by (metis (no_types, lifting) Choice_in_set equals0D)
  define "rd" where 
  "rd = 
  Choice 
  (rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<inter> {f. \<exists>m fl. f = cDIAM m fl})"
  then have "cequiv TYPE('a) (cDIAM m fl) rd"
    using in_rclass_cequiv
    by (metis (no_types, lifting) Int_iff c cequiv_def)
  then obtain m' fl' where "rd = cDIAM m' fl'"
    using c rd_def by blast
  then have eqvd:"cequiv TYPE('a) (cDIAM m fl) (cDIAM m' fl')"
    using \<open>cequiv TYPE('a) (cDIAM m fl) rd\<close> by force
  have "cDIAM m' fl' \<in>  cDIAM_deg_wff_reps TYPE('a) n sig"
    unfolding cDIAM_deg_wff_reps_def
   
    using \<open>rclass (deg_wffs n sig) (cequivr TYPE('a)) (cDIAM m fl) \<in> 
    quotient' (deg_wffs n sig) (cequivr TYPE('a))\<close> 
    \<open>rd = \<diamondsuit>m' fl'\<close> c rd_def by blast
  then show ?thesis using infinite_cDIAM_cong[OF infinite eqvd] assms
   eqvd
    by blast
qed

lemma cDIAM_deg_wff_reps_deg_wffs:
 "cDIAM_deg_wff_reps TYPE('a) n sig \<subseteq> deg_wffs n sig"
  unfolding cDIAM_deg_wff_reps_def Choice_in_set
  by (smt (verit, del_insts) Choice_in_set CollectD DiffE IntE image_iff insertCI quotient'_def rclass_def subsetI)
 
lemma cDIAM_deg_wff_reps_properties':
  assumes "cDIAM m fl \<in> deg_wffs n sig"
    and infinite:"infinite (UNIV::'a set)"
    and sat:"asatis M (w::'a) (cDIAM m fl)"
  shows "\<exists>fl'. cDIAM m fl' \<in> cDIAM_deg_wff_reps TYPE('a) n sig \<and>
    cequiv TYPE('a) (cDIAM m fl) (cDIAM m fl') \<and>
    length fl = length fl' \<and> 
      (\<forall>j. j < length fl \<longrightarrow> cequiv TYPE('a) (fl ! j) (fl' ! j))"
proof - 
  from sat have "\<not>cequiv TYPE('a) (cDIAM m fl) cFALSE"
    by (meson asatis.simps(1) cequiv_def)
  with cDIAM_deg_wff_reps_properties show ?thesis 
  by (metis assms(1) assms(2))
qed



end