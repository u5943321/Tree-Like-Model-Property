(* Title:        Part of the Modal Model Theory project
 * Content:      prop 2.14 from Blackburn et al. regarding preservation of modal structs under
 *               bounded morphisms
 *)

theory Bounded_Morphism
  imports Main Modal_Syntax Modal_Model Modal_Semantics
begin


 definition bounded_morphism :: 
"('m set \<times> ('m \<Rightarrow> nat)) \<times> 'p set \<Rightarrow> 
 ('a \<Rightarrow> 'b) \<Rightarrow> ('m,'p,'a) struct => ('m,'p,'b) struct => bool"
where
"bounded_morphism sig f M M' \<longleftrightarrow> 
 is_struct sig M \<and> is_struct sig M' \<and>
 (\<forall>w. w \<in> world M \<longrightarrow> f w \<in> world M') \<and>
 (\<forall>w p. w \<in> world M \<and> p \<in> props sig \<longrightarrow> valt M p w = valt M' p (f w)) \<and>
 (\<forall>m wl. rel M m wl --> rel M' m (map f wl)) \<and>
 (\<forall>m w v'l. w \<in> world M \<longrightarrow> rel M' m (f w # v'l) \<longrightarrow> 
  (\<exists>vl. rel M m (w # vl) \<and> map f vl = v'l))"

(* from Blackburn prop_2_14 *)
lemma bounded_morphism_modal_eq:
  assumes M1: "is_struct sig M" and M2: "is_struct sig M'"
  and bounded_morph: "bounded_morphism sig f M M'"
  and w_is_world: "w \<in> world M"
  and wf: "wff sig phi"
shows "csatis sig M w phi \<longleftrightarrow> csatis sig M' (f w) phi"
  using wf w_is_world 
proof (induction arbitrary: w rule: wff.induct)
  case cFALSE
  then show ?case by simp
next
  case (cVAR p)
  then show ?case using bounded_morph bounded_morphism_def csatis.simps(2) 
    by (metis (no_types, lifting)) 
next
  case (cDISJ f1 f2)
  then show ?case by simp
next
  case (cNOT f)
  then show ?case using bounded_morph bounded_morphism_def csatis.simps(4) 
    by metis
next
  case (cDIAM m fl)
   assume wwM: " w \<in> world M" 
  with bounded_morph bounded_morphism_def have fwW' : "f w \<in> world M'" 
    by metis
  have
    cwf: "\<forall>f. f \<in> list.set fl \<longrightarrow> wff sig f" using cDIAM.IH by blast
  then show ?case 
  proof (intro iffI)
    assume LHS: "csatis sig M w (cDIAM m fl)" 
    then obtain vl where 
    lenvl: "length vl = length fl" 
    and rwvl:"rel M m (w # vl)" 
    and vlfl: "\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i)"
      unfolding csatis_simps5
      by (meson M1 csatis_simps5)
    from lenvl have lenfvl:"length (map f vl) = length fl" by simp
    from rwvl bounded_morph bounded_morphism_def have fwfvl:"rel M' m (f w # map f vl)"
      by (metis list.simps(9))
    from rwvl M1 have vW: "\<forall>v. v \<in> list.set vl \<longrightarrow> v \<in> world M"
      using is_struct_def
      by (metis list.set_intros(2))
    from cwf vW cDIAM.IH have 
    fvlfl: "\<forall>i<length vl. csatis sig M' (map f vl ! i) (fl ! i)"
     using lenvl vlfl by force
   from LHS show "csatis sig M' (f w) (cDIAM m fl)" unfolding csatis_simps
      using lenfvl fwfvl fvlfl cDIAM.prems fwW' lenvl 
      by (metis (no_types, lifting) M2 cDIAM.hyps(1) cDIAM.hyps(2) csatis_simps5)
     
  next
   assume RHS: "csatis sig M' (f w) (cDIAM m fl)" 
    then obtain v'l where 
    lenv'l: "length v'l = length fl" 
    and fwfvl:"rel M' m (f w # v'l)" 
    and v'lfl: "\<forall>i<length v'l. csatis sig M' (v'l ! i) (fl ! i)"
      unfolding csatis_simps 
      by (meson M2 csatis_simps5)
    from fwfvl bounded_morph wwM obtain vl 
      where rwvl: "rel M m (w # vl)"
        and fvl : "map f vl = v'l" 
      unfolding bounded_morphism_def
      by metis
    from fvl lenv'l have lenvl:"length vl = length fl" 
      by fastforce
    from rwvl M1 have vW: "\<forall>v. v \<in> list.set vl \<longrightarrow> v \<in> world M"
      using is_struct_def
      by (metis list.set_intros(2))
    with vW cDIAM.IH have 
    vlfl: "\<forall>i<length vl. csatis sig M (vl ! i) (fl ! i)"
     using lenvl v'lfl cwf fvl by force
   from RHS show "csatis sig M w (cDIAM m fl)" unfolding csatis_simps
      using lenvl fwfvl vlfl cDIAM.prems rwvl 
      by (metis (no_types, lifting) M1 cDIAM.hyps(1) cDIAM.hyps(2) csatis_simps5)
  qed
qed

lemmas Blackburn_prop_2_14 = bounded_morphism_modal_eq

end