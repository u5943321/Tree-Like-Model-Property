(* Title:        Part of the Modal Model Theory project
 * Content:      Definition of a tree, generalizing the definition 
                 written in Blackburn et al.
                 Construct tree-like model as in Blackburn et al. 
 *)


theory Tree_Like_Model
  imports Main Modal_Syntax Modal_Model Modal_Semantics 
          Bounded_Morphism Generated_Submodel
begin

definition tree :: "'m set \<Rightarrow> ('m,'a) frame \<Rightarrow> 'a \<Rightarrow> bool" where
"tree Op F r \<equiv>
 r \<in> fworld F \<and>
 (\<forall>t. t \<in> fworld F \<longrightarrow> 
  (r,t) \<in> (gen_birel Op (restrict_rel (frel F) (fworld F)))\<^sup>*) \<and>
 (\<forall>t. t \<in> fworld F \<longrightarrow> t \<noteq> r \<longrightarrow> 
   (\<exists>! t'. t' \<in> fworld F \<and> (t',t) \<in> gen_birel Op (restrict_rel (frel F) (fworld F)))) \<and> 
 (\<forall>t. t \<in> fworld F \<longrightarrow> (t,t) \<notin> (gen_birel Op (restrict_rel (frel F) (fworld F)))\<^sup>+)"

definition rset :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b list \<Rightarrow> bool)  \<Rightarrow> 'b set"
  where 
"rset \<tau> R =  {v. \<exists>m vl. m \<in> \<tau> \<and> R m vl \<and> v \<in> set vl}"

lemma subseteq_restrict_rel:
  assumes "rset Op R \<subseteq> W"
  shows "(gen_birel Op (restrict_rel R W)) = 
         (gen_birel Op R)" using assms 
  unfolding rset_def restrict_rel_def gen_birel_def
  by blast



lemma gen_birel_rset1:
  assumes "(w1, w2) \<in> gen_birel \<tau> R"
  shows "w1 \<in> rset \<tau> R" 
  by (smt (verit, ccfv_SIG) Product_Type.Collect_case_prodD assms 
gen_birel_def list.set_intros(1) mem_Collect_eq rset_def split_pairs)

lemma gen_birel_rset2:
  assumes "(w1, w2) \<in> gen_birel \<tau> R"
  shows "w2 \<in> rset \<tau> R" unfolding gen_birel_def rset_def
  by (smt (verit, best) assms case_prodD gen_birel_def list.set_intros(2) mem_Collect_eq)

lemma tree_R_subseteq_W:
  assumes a:"rset Op (frel F) \<subseteq> (fworld F)"
  shows
  "tree Op F r \<equiv>
 r \<in> fworld F \<and>
 (\<forall>t. t \<in> fworld F \<longrightarrow> (r,t) \<in> (gen_birel Op (frel F))\<^sup>*) \<and>
 (\<forall>t. t \<in> fworld F \<longrightarrow> t \<noteq> r \<longrightarrow> (\<exists>! t'. (t',t) \<in> gen_birel Op (frel F))) \<and> 
 (\<forall>t. t \<in> fworld F \<longrightarrow> (t,t) \<notin> (gen_birel Op (frel F))\<^sup>+)"
  unfolding tree_def
  using subseteq_restrict_rel[OF a] gen_birel_rset1
   rset_def
  by (smt (z3) assms fst_conv in_mono)
 
lemma tree_ss_alt:
  assumes a:"rset Op R \<subseteq> W"
  shows
  "tree Op (W,R) r \<equiv>
 r \<in> W \<and>
 (\<forall>t. t \<in> W \<longrightarrow> (r,t) \<in> (gen_birel Op R)\<^sup>*) \<and>
 (\<forall>t. t \<in> W \<longrightarrow> t \<noteq> r \<longrightarrow> (\<exists>! t'. (t',t) \<in> gen_birel Op R)) \<and> 
 (\<forall>t. t \<in> W \<longrightarrow> (t,t) \<notin> (gen_birel Op R)\<^sup>+)"
  using tree_R_subseteq_W[of Op "(W,R)",unfolded fst_conv snd_conv]
  using assms by presburger
 


inductive_set unrav_seq ::
 "'a \<Rightarrow> 'm set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> ('a list set)"
 for w :: "'a" and Op :: "'m set" and R ::"'m \<Rightarrow> 'a list \<Rightarrow> bool"
 where 
  "[w] \<in> unrav_seq w Op R"
| "l \<in> unrav_seq w Op R \<Longrightarrow> m \<in> Op \<Longrightarrow> R m (last l # vl) \<Longrightarrow>
    n < length vl \<Longrightarrow> l @ [vl ! n] \<in> unrav_seq w Op R "

definition unrav_rel ::
 "'a \<Rightarrow>'m set \<Rightarrow> ('m \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> ('m \<Rightarrow> 'a list list \<Rightarrow> bool)"
 where
 "unrav_rel w Op R m ll \<equiv> 
  
  (\<forall>l. l \<in> list.set ll \<longrightarrow> l \<in> unrav_seq w Op R) \<and>
  (\<forall>n. 0 < n \<longrightarrow> n < length ll \<longrightarrow> length (ll ! n) = length (hd ll) + 1 ) \<and>
  (\<forall>n l. n < length (hd ll) \<longrightarrow> l \<in> list.set ll \<longrightarrow> l! n = (hd ll) ! n) \<and>
  m \<in> Op \<and> R m (map last ll) "


lemma unrav_rel_Cons_hd_length:
"unrav_rel w Op R m (wl # exts) \<Longrightarrow> l \<in> list.set exts \<Longrightarrow> 
 length l = length wl + 1"
  unfolding unrav_rel_def
  by (smt (verit, ccfv_SIG) Suc_length_conv
   in_set_conv_nth less_Suc_eq_0_disj list.sel(1) nth_Cons_Suc)


lemma unrav_rel_take:
"unrav_rel w Op R m ll \<Longrightarrow> l \<in> list.set ll \<longrightarrow> take (length (hd ll)) l = (hd ll) "
  unfolding unrav_rel_def using unrav_rel_Cons_hd_length
  by (smt (verit, ccfv_SIG) dual_order.refl gr0I in_set_conv_nth 
le_add_same_cancel1 list.sel(1) list.set_cases nth_Cons_0 nth_take_lemma
 take_all zero_less_one_class.zero_le_one)

lemma unrav_rel_alt :
 "unrav_rel w Op R m ll \<equiv> 
 (\<forall>l. l \<in> list.set ll \<longrightarrow> l \<in> unrav_seq w Op R) \<and>
  (\<forall>n. 0 < n \<longrightarrow> n < length ll \<longrightarrow> length (ll ! n) = length (hd ll) + 1 ) \<and>
  (\<forall>l.  l \<in> list.set ll \<longrightarrow> take (length (hd ll)) l = hd ll ) \<and>
  m \<in> Op \<and> R m (map last ll)
" unfolding unrav_rel_def using unrav_rel_take 
  by (smt (verit, del_insts) nth_take unrav_rel_def)

lemma unrav_rel_ss_unrav_seq :
"rset Op (unrav_rel w Op R) \<subseteq> unrav_seq w Op R"
  unfolding rset_def unrav_rel_def
  by blast

lemma unrav_from_a_list:
  assumes m: "(m::'m)\<in> Op" 
  and rwvl: "R m (w # vl)" 
  and l: "l \<in> unrav_seq w0 Op R" 
  and lw: "last l = w"
shows "unrav_rel w0 Op R m (l # map (\<lambda>v. l @ [v]) vl) "
  unfolding unrav_rel_alt
proof (intro conjI) 
  show "\<forall>la. la \<in> list.set (l # map (\<lambda>v. l @ [v]) vl) \<longrightarrow> la \<in> unrav_seq w0 Op R" 
    using l unrav_seq.simps m rwvl lw
    by (smt (verit) in_set_conv_nth length_map  nth_map set_ConsD)
next 
  show "\<forall>n>0. n < length (l # map (\<lambda>v. l @ [v]) vl) \<longrightarrow> length ((l # map (\<lambda>v. l @ [v]) vl) ! n) = 
    length (hd (l # map (\<lambda>v. l @ [v]) vl)) + 1"
    by auto
next show "m \<in> Op" using m.
next show "R m (map last (l # map (\<lambda>v. l @ [v]) vl))" using lw rwvl 
  proof -
    have mm: "(map last (l # map (\<lambda>v. l @ [v]) vl)) = 
         last l # map last (map (\<lambda>v. l @ [v]) vl)"
      by auto
    have "map last (map (\<lambda>v. l @ [v]) vl) = vl" 
      by (simp add: map_idI)
    with mm lw have "(map last (l # map (\<lambda>v. l @ [v]) vl)) = w # vl"
      by argo
    then show ?thesis
      using rwvl by auto
  qed
next show "\<forall>la. la \<in> list.set (l # map (\<lambda>v. l @ [v]) vl) \<longrightarrow>
         take (length (hd (l # map (\<lambda>v. l @ [v]) vl))) la = 
hd (l # map (\<lambda>v. l @ [v]) vl)" 
    by fastforce
  
qed

lemma unrav_seq_nnil:
   "l \<in> unrav_seq w Op R \<Longrightarrow> l \<noteq> []"
proof (induction rule: unrav_seq.induct)
  case (1)
  then show ?case by simp
next
  case (2 l m vl n)
  then show ?case by simp
qed

lemma tree_unrav_cond1_conn_from_root :
  fixes t
  assumes t:" t \<in> unrav_seq w (Op::'m set) R "
  shows "([w], t) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>*"

proof (induct_tac rule: unrav_seq.induct)
  show "t \<in> unrav_seq w Op R" using t.
next 
   show "([w], [w]) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>*"
    by blast
next 
  fix l m fix vl:: "'a list" fix n:: "nat"
  assume n:"n < length vl"
  and lseq : "l \<in> unrav_seq w Op R "
  and wl: "([w], l) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>*"
  and m : " m \<in> Op "
  and llvl : "R m (last l # vl)"
  have lnn:"l \<noteq> []" using unrav_seq_nnil[OF lseq].
  have 2:"unrav_rel w Op R m (l # map (\<lambda>v. l @ [v]) vl)" 
    using 
    unrav_from_a_list [OF m, of "R" "last l" "vl", OF llvl lseq]
    by auto
  have 3:"l @ [vl ! n] \<in> list.set (map (\<lambda>v. l @ [v]) vl)" 
    using n by auto
  have "(l,l @ [vl ! n]) \<in> gen_birel Op (unrav_rel w Op R)"
    unfolding gen_birel_def using m 2 3
    by blast
  with wl show "([w], l @ [vl ! n]) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>*"
    by simp
qed


lemma unrav_rel_length:
  assumes "unrav_rel w Op R m (wl # exts)" and "l \<in> list.set exts"
  shows "length wl < length l" using assms
  unfolding unrav_rel_def 
  by (smt (verit, ccfv_threshold) add.commute 
add.right_neutral add_Suc_right in_set_conv_nth length_pos_if_in_set 
less_one list.sel(1) list.size(4) 
nat_add_left_cancel_less nth_Cons_Suc zero_less_Suc)


lemma unrav_rel_trancl_length:
  assumes "(t1, t2) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>+"
  shows "length t1 < length t2" using assms
proof (induction rule:trancl.induct)
  case (r_into_trancl a b)
  then show ?case unfolding gen_birel_def using unrav_rel_length 
    by fastforce 
next
  case (trancl_into_trancl a b c)
  then have "length b < length c" using unrav_rel_length 
    by (smt (verit) case_prodD gen_birel_def mem_Collect_eq)
  then show ?case
    using dual_order.strict_trans trancl_into_trancl.IH by blast
qed

lemma unrav_rel_pred_if_ex_then_unique:
  assumes "unrav_rel w Op R m (wl # exts)" 
      and "unrav_rel w Op R m (wl' # exts')"
      and "l \<in> list.set exts"
      and "l \<in> list.set exts'"
    shows "wl = wl'" using assms unfolding unrav_rel_alt
  by (metis add_right_imp_eq assms(1) assms(2) list.sel(1)
      list.set_intros(2) unrav_rel_Cons_hd_length)

lemma unrav_seq_pred_ex:
  assumes "wl \<in> unrav_seq w0 Op R" and "length wl \<noteq> 1" shows
  "(take (length wl - 1) wl,wl) \<in> (gen_birel Op (unrav_rel w0 Op R))" using assms
proof (induction rule:unrav_seq.induct)
  case 1 then have "False" by simp
  then show ?case by simp
next
  case (2 l m vl n)
  then show ?case unfolding gen_birel_def  using unrav_from_a_list
  proof - 
    assume l: "l \<in> unrav_seq w0 Op R"
       and m: "m \<in> Op"
       and llvl: "R m (last l # vl)"
    have "take (length (l @ [vl ! n]) - 1) (l @ [vl ! n]) = l"
      by auto
    have "unrav_rel w0 Op R m (l # map (\<lambda>v. l @ [v]) vl)" 
      using unrav_from_a_list[of m Op R "last l" vl l, OF m llvl] 
            l by auto
    show "(take (length (l @ [vl ! n]) - 1) (l @ [vl ! n]), l @ [vl ! n])
    \<in> {(w, u). \<exists>m ul. m \<in> Op \<and> unrav_rel w0 Op R m (w # ul) \<and> u \<in> list.set ul} " 
    using "2.hyps"(4) \<open>unrav_rel w0 Op R m (l # map (\<lambda>v. l @ [v]) vl)\<close> m by fastforce
qed
qed

lemma unrav_seq_cond2_sing_length1: 
"t \<in> unrav_seq w Op R \<Longrightarrow> t \<noteq> [w] \<Longrightarrow> length t > 1"
proof (induction rule:unrav_seq.induct)
  case 1 then have "False"
    by fastforce
  then show ?case  by auto
next
  case (2 l m vl n)
  then show ?case using unrav_seq_nnil 
    by auto
qed


lemma unrav_seq_tree_cond3:
"t \<in> unrav_seq w Op R \<Longrightarrow>
       t \<noteq> [w] \<Longrightarrow>
       (t', t) \<in> gen_birel Op (unrav_rel w Op R) \<Longrightarrow>
       (y, t) \<in> gen_birel Op (unrav_rel w Op R) \<Longrightarrow> t' = y"
  unfolding gen_birel_def
  by safe (metis add_right_imp_eq list.sel(1) list.set_intros(2) 
  unrav_rel_Cons_hd_length unrav_rel_take)

lemma tree_unrav :
 "tree Op (unrav_seq w Op R,unrav_rel w Op R) [w]"
proof -
  have "\<And>t. t \<in> unrav_seq w Op R \<Longrightarrow> ([w], t) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>*"
    using tree_unrav_cond1_conn_from_root.
  moreover have "\<And>t. t \<in> unrav_seq w Op R \<Longrightarrow> t \<noteq> [w] \<Longrightarrow> 
       \<exists>t'. (t', t) \<in> gen_birel Op (unrav_rel w Op R)" 
     using unrav_seq_cond2_sing_length1 unrav_seq_pred_ex 
     by (metis less_numeral_extra(4)) 
  moreover have "\<And>t t' y.
       t \<in> unrav_seq w Op R \<Longrightarrow>
       t \<noteq> [w] \<Longrightarrow>
       (t', t) \<in> gen_birel Op (unrav_rel w Op R) \<Longrightarrow>
       (y, t) \<in> gen_birel Op (unrav_rel w Op R) \<Longrightarrow> t' = y" 
  using unrav_seq_tree_cond3.
  moreover have "\<And>t. t \<in> unrav_seq w Op R \<Longrightarrow> 
    (t, t) \<in> (gen_birel Op (unrav_rel w Op R))\<^sup>+ \<Longrightarrow> False " 
    using unrav_rel_trancl_length 
    by (metis nat_less_le)
  ultimately show ?thesis using  tree_R_subseteq_W 
    by (smt (verit, del_insts) fst_conv snd_conv unrav_rel_ss_unrav_seq unrav_seq.intros(1))
   
qed

definition unrav_valt :: "'a list set \<Rightarrow> ('p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'a list \<Rightarrow> bool)" where 
"unrav_valt seqs v = (\<lambda> p wl. wl \<in> seqs \<and> v p (last wl))"

lemma unrav_rel_msyms:
   "unrav_rel w ms (rel M) m wl \<Longrightarrow> m \<in> ms"
  unfolding unrav_rel_def by simp

lemma unrav_rel_marity:
assumes M: "is_struct sig M" and w:"w \<in> world M"
shows "unrav_rel w ms (rel M) m wl \<Longrightarrow> length wl = Suc (arity sig m)"
  using assms
  unfolding is_struct_def unrav_rel_def 
  by (metis Suc_eq_plus1 length_map)
 


lemma unrav_is_struct:
  assumes M: "is_struct sig M" and w:"w \<in> world M"
  shows "is_struct sig 
  (unrav_seq w (ops sig) (rel M),
   unrav_rel w (ops sig) (rel M), 
   unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M))"
  unfolding is_struct_def fst_conv snd_conv
proof(intro conjI allI impI)
  show "unrav_seq w (ops sig) (rel M) \<noteq> {}" 
    using unrav_seq.intros(1) by fastforce
  show "\<And>m wl. unrav_rel w (ops sig) (rel M) m wl \<Longrightarrow> length wl = (arity sig m) + 1"
    using unrav_rel_marity 
    by (metis M add.commute plus_1_eq_Suc w)
  show "\<And>m wl. unrav_rel w (ops sig) (rel M) m wl \<Longrightarrow> m \<in> ops sig"
    using unrav_rel_msyms.
  show "\<And>m wl wa.
       unrav_rel w (ops sig) (rel M) m wl \<Longrightarrow>
       wa \<in> list.set wl \<Longrightarrow> wa \<in> unrav_seq w (ops sig) (rel M)"
    using unrav_rel_def
    by metis
  show "\<And>p wa. 
   unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M) p wa \<Longrightarrow> p \<in> props sig"
    using assms 
    by (metis is_struct_def unrav_valt_def)
  show "\<And>p wa.
       unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M) p wa \<Longrightarrow>
       wa \<in> unrav_seq w (ops sig) (rel M)"
    using unrav_rel_def
    by (simp add: unrav_valt_def)
qed


lemma Blackburn_prop_2_15_bounded_morphism_in_world:
   assumes w: "w \<in> world M" and M: "is_struct sig M"
  shows "vl \<in> unrav_seq w (msyms sig) (rel M) \<Longrightarrow> v \<in> list.set vl \<Longrightarrow>
         v \<in> world M"
proof (induction rule:unrav_seq.induct)
  case 1
  then show ?case using w by auto 
next
  case (2 l m vl n)
  then show ?case using M unfolding is_struct_def
    by fastforce 
qed



lemma Blackburn_prop_2_15_bounded_morphism_last_cond:
assumes w: "w \<in> world M" and M: "is_struct sig M"
and wl: "wl \<in> unrav_seq w (ops sig) (rel M)"
and r: "rel M m (last wl # v'l)"
shows " \<exists>vl. unrav_rel w (ops sig) (rel M) m (wl # vl) \<and> map last vl = v'l"
  using  unrav_from_a_list
proof -
  from r have m:"m \<in> ops sig" using is_struct_def 
    by (metis M)
  have 2:"map last (map (\<lambda>v. wl @ [v]) v'l) = v'l " 
    by (simp add: list.map_ident_strong)
  have 1:"unrav_rel w (ops sig) (rel M) m (wl #  (map (\<lambda>v. wl @ [v]) v'l))"
    using  
  unrav_from_a_list[of m "(ops sig)" "rel M" "last wl" "v'l" "wl" "w",
                    OF m r wl] 
    by blast
  with 2 show "\<exists>vl. unrav_rel w (ops sig) (rel M) m (wl # vl) \<and> map last vl = v'l"
    by blast
qed

lemma Blackburn_prop_2_15_bounded_morphism: 
  assumes w: "w \<in> world M" and M: "is_struct sig M"
  shows 
  "bounded_morphism sig last 
  (unrav_seq w (ops sig) (rel M),
  unrav_rel w (ops sig) (rel M), 
  unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M))
  M"
  unfolding bounded_morphism_def fst_conv snd_conv (* apply auto*)
proof (intro conjI impI allI) 
  show "is_struct sig M" using M.
  show
  "is_struct sig
     (unrav_seq w (ops sig) (rel M), unrav_rel w (ops sig) (rel M),
      unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M))"
    using unrav_is_struct[of sig M, OF M w].
  show " \<And>wa. wa \<in> unrav_seq w (ops sig) (rel M) \<Longrightarrow> last wa \<in> world M"
    using Blackburn_prop_2_15_bounded_morphism_in_world[OF w M] 
    by (simp add: unrav_seq_nnil)
  have veq:"\<And>wa p.
       wa \<in> unrav_seq w (ops sig) (rel M) \<Longrightarrow>
       p \<in> props sig \<Longrightarrow> 
  unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M) p wa = valt M p (last wa)"
    using unrav_valt_def by metis
  show "\<And>wa p.
       wa \<in> unrav_seq w (ops sig) (rel M) \<and> p \<in> props sig \<Longrightarrow>
       unrav_valt (unrav_seq w (ops sig) (rel M)) (valt M) p wa = valt M p (last wa)" using veq
    by blast
  show "\<And>m wl. unrav_rel w (ops sig) (rel M) m wl \<Longrightarrow> rel M m (map last wl)"
    unfolding unrav_rel_def by auto
  show "\<And>m wa v'l.
       wa \<in> unrav_seq w (ops sig) (rel M) \<Longrightarrow> rel M m (last wa # v'l) \<Longrightarrow>
    \<exists>vl. unrav_rel w (ops sig) (rel M) m (wa # vl) \<and> map last vl = v'l "
    using Blackburn_prop_2_15_bounded_morphism_last_cond 
    by (metis M w)
qed  

lemma  tree_like_property:
  assumes M:"is_struct sig M" 
  and phi: "wff sig phi"
  and s0: "csatis sig M w phi"
shows "\<exists>M' . is_struct sig M'\<and> tree (ops sig) (world M',rel M') [w] \<and> csatis sig M' [w] phi"
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
  have "[w] \<in> W'" 
    unfolding W'_def 
    by (simp add: unrav_seq.intros(1))
  then have wW':"[w] \<in> world (W',R',V')" by simp
  have "csatis sig (W',R',V') [w] phi" 
    unfolding M1_def
    using Blackburn_prop_2_14 [of sig "(W',R',V')" M1,OF M' M1 bounded_morphism wW' phi,unfolded M1_def] sr
    by auto
  then show ?thesis using t 
    using M1_def R'_def W'_def M' by auto
qed


lemma  tree_like_property':
  assumes M:"is_struct sig M" 
  and phi: "wff sig phi"
  and s0: "asatis M w phi"
shows "\<exists>M' . is_struct sig M' \<and> tree (ops sig) (world M',rel M') [w] \<and> asatis M' [w] phi"
  using tree_like_property csatis_asatis
   by (metis M phi s0)

lemmas Blackburn_prop_2_15 = tree_like_property


end