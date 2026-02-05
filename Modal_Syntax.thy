(* Title:        Part of the Modal Model Theory project
 * Content:      syntax of modal formulas, signature, propositional formulas,
 *               propositional letters, substitution, degree of formulas
 *)

theory Modal_Syntax
  imports Main
begin

datatype ('m,'p) cform = cVAR "'p"
  | cFALSE
  | cDISJ "('m,'p) cform" "('m,'p) cform" 
  | cNOT "('m,'p) cform"
  | cDIAM 'm "(('m,'p) cform) list" ("\<diamondsuit>_ _" [0, 0])


abbreviation mops :: "'m set \<times> ('m \<Rightarrow> nat) \<Rightarrow> 'm set" where
"mops \<tau> \<equiv> fst \<tau>"

abbreviation marity :: "'m set \<times> ('m \<Rightarrow> nat) \<Rightarrow> ('m \<Rightarrow> nat)" where
"marity \<tau> \<equiv> snd \<tau>"

type_synonym ('m,'p) sig = 
"('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set "

type_synonym 'm msig = 
"('m set \<times> ('m \<Rightarrow> nat))"

abbreviation props :: 
"('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> 'p set" where
"props sig \<equiv> snd sig"

abbreviation ops :: 
"('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> 'm set" where
"ops sig \<equiv> fst (fst sig)"

abbreviation arity :: 
"('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> 'm \<Rightarrow> nat" where
"arity sig \<equiv> snd (fst sig)"

inductive wff :: \<open>('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> ('m, 'p) cform \<Rightarrow> bool\<close>
  for sig :: "('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set" 
  where
    cFALSE: "wff sig cFALSE" 
  | cVAR: "p \<in> props sig \<Longrightarrow> wff sig (cVAR p) "
  | cDISJ: "wff sig (cDISJ f1 f2)" if "wff sig f1" "wff sig f2 "
  | cNOT: "wff sig (cNOT f)" if "wff sig f"
  | cDIAM: "wff sig (cDIAM m fl) "
    if "m \<in> ops sig" "length fl = (arity sig m)" "\<forall>f. f \<in> list.set fl \<longrightarrow>
      wff sig f"

definition cCONJ where
 "cCONJ f1 f2 \<equiv> cNOT (cDISJ (cNOT f1) (cNOT f2))"

definition cTRUE where
 "cTRUE \<equiv> cNOT cFALSE"

lemma wff_cFALSE:
 "wff sig cFALSE" 
  using cFALSE by blast

lemma wff_cVAR:
 "wff sig (cVAR a) \<longleftrightarrow>(a \<in> props sig)"
proof -
  have "wff sig (cVAR a) \<Longrightarrow> a \<in> props sig"
    by (metis cform.distinct(1) cform.distinct(3) cform.distinct(5) 
cform.distinct(7) cform.inject(1) wff.simps)
  have " a \<in> props sig \<Longrightarrow> wff sig (cVAR a)"
    by (simp add: cVAR)
  show ?thesis 
    using \<open>a \<in> props sig \<Longrightarrow> wff sig (cVAR a)\<close> \<open>wff sig (cVAR a) \<Longrightarrow> a \<in> props sig\<close> by blast
qed




lemma wff_cDISJ:
 "wff sig (cDISJ f1 f2)\<equiv>  wff sig f1 \<and> wff sig f2"
  by (smt (verit, best) cDISJ cform.inject(2) cform.simps(14)
  cform.simps(20) cform.simps(22) cform.simps(8) wff.cases)

lemma wff_cNOT:
 "wff sig (cNOT f) \<equiv> wff sig f" 
  by (smt (verit, best) cform.distinct(11) cform.distinct(15)
 cform.distinct(19) cform.distinct(5) cform.inject(3) wff.simps)

lemma wff_cDIAM:
 "wff sig (cDIAM m fl) \<equiv> 
  m \<in> ops sig \<and> length fl = (arity sig m) \<and>
  (\<forall>f. f \<in> list.set fl \<longrightarrow>
      wff sig f)" 
  by (smt (verit, best) cform.distinct(13) cform.distinct(19) 
cform.distinct(7) cform.inject(4) cform.simps(22) wff.simps)



fun deg :: " ('m,'p) cform \<Rightarrow> nat" where 
    "deg cFALSE = 0"
  | "deg (cVAR p) = 0"
  | "deg (cNOT phi) = deg phi"
  | "deg (cDISJ f1 f2) = max (deg f1) (deg f2)"
  | "deg (cDIAM f fl) = (if fl = [] then 1 else 1 + Max (deg ` (list.set fl)))" 



lemma deg_cDIAM_bound:
  assumes "deg (cDIAM m fl) \<le> n + 1"
  and "f \<in> set fl" 
shows "deg f \<le> n" using assms finite_set
  unfolding deg.simps 
  by (smt (verit, del_insts) Max.bounded_iff add.commute empty_iff 
      image_eqI list.set(1) list.set_map nat_add_left_cancel_le)
 

lemma subst_termination_helper: 
\<open>x \<in> list.set fl \<Longrightarrow>
       size x < Suc (size_list size fl)\<close>
proof (induction fl arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a fl)
  then show ?case 
    by (meson Suc_n_not_le_n in_set_zipE linorder_le_less_linear size_list_estimation')
qed

lemma wf_size_subst: "wf {(( c, d),  g, h). size d < size h}"
unfolding wfP_wf_eq[symmetric]
by (rule wfP_if_convertible_to_nat[of _ \<open>\<lambda>( c, d). size d\<close>])
auto

function subst :: "('q \<Rightarrow> ('m,'p) cform) \<Rightarrow> ('m,'q) cform \<Rightarrow> ('m,'p) cform"
  where 
   "subst f cFALSE = cFALSE"
 | "subst f (cVAR p) = f p"
 | "subst f (cDISJ f1 f2) = cDISJ (subst f f1) (subst f f2)"
 | "subst f (cNOT fm) = cNOT (subst f fm)"
 | "subst f (cDIAM m fl) = cDIAM m (map (subst f) fl)" 
proof-
  show "\<And>P x. (\<And>f. x = (f, cFALSE) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>f p. x = (f, cVAR p) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>f f1 f2. x = (f, cDISJ f1 f2) \<Longrightarrow> P) \<Longrightarrow>
           (\<And>f fm. x = (f, cNOT fm) \<Longrightarrow> P) \<Longrightarrow> (\<And>f m fl. x = (f, \<diamondsuit>m fl) \<Longrightarrow> P) \<Longrightarrow> P"
   by (metis cform.exhaust old.prod.exhaust)
qed auto
termination 
  by (relation \<open>{((c,d),g,h). size d < size h}\<close>)
(auto simp: subst_termination_helper wf_size_subst)


fun prop_letters:: "('m, 'p) cform \<Rightarrow> 'p set" 
  where 
   "prop_letters cFALSE = {}" 
 | "prop_letters (cVAR p) = {p}" 
 | "prop_letters (cDISJ f1 f2) = 
    prop_letters f1 \<union> prop_letters f2"
 | "prop_letters (cNOT f) = prop_letters f"
 | "prop_letters (cDIAM m fl) = 
   \<Union> (list.set (list.map prop_letters fl))"


lemma subst_prop_letters:
  assumes plf:"prop_letters phi \<subseteq> s"
      and f12: "\<And>p. p \<in> s \<Longrightarrow> f1 p = f2 p"
    shows "subst f1 phi = subst f2 phi" using assms
proof (induction phi rule:cform.induct)
qed auto

inductive prop_cform :: "('m,'p) cform \<Rightarrow> bool" where
   "prop_cform cFALSE"
 | "prop_cform (cVAR p)"
 | "prop_cform f \<Longrightarrow> prop_cform (cNOT f)"
 | "prop_cform f1 \<Longrightarrow> prop_cform f2 \<Longrightarrow> 
    prop_cform (cDISJ f1 f2)"


lemmas prop_cform_FALSE=Modal_Syntax.prop_cform.intros(1)

lemmas prop_cform_cVAR=Modal_Syntax.prop_cform.intros(2)

lemma prop_cform_cNOT:
 "prop_cform (cNOT f) \<equiv> prop_cform f" 
  by (smt (verit, best) cform.distinct(15) cform.distinct(5)
  cform.inject(3) cform.simps(16) prop_cform.simps)

lemma prop_cform_cDISJ:
 "prop_cform (cDISJ f1 f2) \<equiv> prop_cform f1 \<and> prop_cform f2" 
  by (smt (verit, ccfv_threshold) cform.distinct(15) cform.inject(2)
  cform.simps(14) cform.simps(8) prop_cform.cases prop_cform.intros(4))

lemma prop_cform_cDIAM:
 "\<not>prop_cform (cDIAM m fl)" 
  using prop_cform.cases by blast

lemma deg_0_propform: 
"deg f = 0 \<equiv> prop_cform f"
proof (induction f)
  case (cVAR x)
  then show ?case
    by (simp add: prop_cform.intros(2))
next
  case cFALSE
  then show ?case 
    by (simp add: prop_cform.intros(1))
next
  case (cDISJ f1 f2)
  then show ?case 
    using prop_cform.cases prop_cform.intros(4) by auto
next
  case (cNOT f)
  then show ?case 
    using prop_cform.cases prop_cform.intros(3) by auto
next
  case (cDIAM x1a x2)
  then show ?case 
    using prop_cform.cases by auto
qed

lemma wff_prop_cform:
  assumes "prop_cform f"
  shows "wff sig f \<equiv> prop_letters f \<subseteq> props sig" using assms
proof (induction f)
  case 1
  then show ?case by (simp add: wff.cFALSE)
next
  case (2 p)
  then show ?case by (simp add: wff_cVAR)
next
  case (3 f)
  then show ?case by (simp add: wff_cNOT)
next
  case (4 f1 f2)
  then show ?case by (simp add: wff_cDISJ)
qed

lemma subst_cDISJ:
  assumes "subst \<sigma> phi0 = cDISJ phi1 phi2"
      and "!p. cVAR p \<noteq> phi0"
    shows "\<exists>phi01 phi02. 
            phi0 = cDISJ phi01 phi02 \<and>
            subst \<sigma> phi01 = phi1 \<and> subst \<sigma> phi02 = phi2" using assms
proof (induction phi0 arbitrary: phi1 phi2 rule: cform.induct)
qed simp_all

lemma subst_cNOT:
  assumes "subst \<sigma> phi0 = cNOT phi"
      and "!p. cVAR p \<noteq> phi0"
    shows "\<exists>phi00.
            phi0 = cNOT phi00 \<and>
            subst \<sigma> phi00 = phi" using assms
proof (induction phi0 arbitrary: phi00 rule: cform.induct)
qed simp_all



lemma deg_cDIAM_Suc0:
 "deg (cDIAM m fl) \<le> n + (1::nat) \<longleftrightarrow> 
( \<forall>f \<in> (deg ` set fl). f \<le> n)"
unfolding deg.simps(5)
  by simp

lemma deg_cDIAM_Suc:
 "deg (cDIAM m fl) \<le> n + (1::nat) \<equiv> 
 \<forall>f \<in> set fl. deg f \<le> n"
  unfolding deg.simps(5) 
  by (smt (z3) deg.simps(5) deg_cDIAM_Suc0 imageE imageI)

lemma cDIAM_in_Union:
 "cDIAM m fl \<in> {cVAR v| v. P v} \<union> X \<equiv> cDIAM m fl \<in> X"
  by auto

lemma prop_letters_cDIAM_subseteq:
  "prop_letters (cDIAM m fl) \<subseteq> s \<equiv> 
  \<forall>f. f \<in> set fl \<longrightarrow> prop_letters f \<subseteq> s"
  unfolding prop_letters.simps(5)
  by (smt (verit, best) UN_subset_iff set_map)



fun modal_operators:: "('m, 'p) cform \<Rightarrow> 'm set" 
  where 
   "modal_operators cFALSE = {}" 
 | "modal_operators (cVAR p) = {}" 
 | "modal_operators (cDISJ f1 f2) = 
    modal_operators f1 \<union> modal_operators f2"
 | "modal_operators (cNOT f) = modal_operators f"
 | "modal_operators (cDIAM m fl) = 
   {m} \<union> \<Union> (list.set (list.map modal_operators fl))"



lemma modal_operators_cDIAM_subseteq:
  "modal_operators (cDIAM m fl) \<subseteq> s \<equiv> 
  m \<in> s \<and> (\<forall>f. f \<in> set fl \<longrightarrow> modal_operators f \<subseteq> s)"
  unfolding modal_operators.simps(5)
  
  by (smt (verit) UN_subset_iff insert_is_Un insert_subset list.set_map)


lemma modal_operators_cVAR:
" \<Union> (modal_operators ` (cVAR ` s)) = {}"
  by fastforce


lemma modal_operators_finite:
 "finite (modal_operators \<phi>)"
proof (induction \<phi>)
  case (cVAR x)
  then show ?case 
    by simp
next
  case cFALSE
  then show ?case 
    by auto
next
  case (cDISJ x1a x2)
  then show ?case
    by auto
next
  case (cNOT x)
  then show ?case 
    by auto
next
  case (cDIAM x1a x2)
  then show ?case unfolding modal_operators.simps by simp 
qed



lemma prop_letters_finite:
 "finite (prop_letters \<phi>)"
proof (induction \<phi>)
  case (cVAR x)
  then show ?case 
    by simp
next
  case cFALSE
  then show ?case 
    by auto
next
  case (cDISJ x1a x2)
  then show ?case
    by auto
next
  case (cNOT x)
  then show ?case 
    by auto
next
  case (cDIAM x1a x2)
  then show ?case by simp 
qed


end